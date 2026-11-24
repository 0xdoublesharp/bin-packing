import Optimality

set_option warningAsError true

namespace Packing.ExactGrid

structure Placement where
  slot : Nat
  piece : Piece

def inventory (certificate : Certificate) : List Stock :=
  let cap := certificate.layoutCount - 1
  certificate.stock.flatMap (fun stock => List.replicate (min cap (stock.limit.getD cap)) stock)

def instances (certificate : Certificate) : List Demand :=
  certificate.demands.flatMap (fun demand => List.replicate demand.quantity demand)

def Admitted (available : List Stock) (demand : Demand) (placement : Placement) : Prop :=
  ∃ stock, available[placement.slot]? = some stock ∧
    Matches placement.piece demand ∧ Fits stock placement.piece

def choices (available : List Stock) (demand : Demand) : List Placement :=
  (List.range available.length).flatMap fun slot =>
    match available[slot]? with
    | none => []
    | some stock =>
      demand.orientations.flatMap fun (rotation, extent) =>
        (Optimality.cells ⟨0, 0, 0⟩ stock.bounds).filterMap fun cell =>
          let piece := Piece.mk demand.name (Optimality.cellPoint cell) extent rotation
          if Fits stock piece then some ⟨slot, piece⟩ else none

private theorem admitted_in_bounds {stock : Stock} {piece : Piece} (h : Fits stock piece) :
    piece.origin.x < stock.bounds.x ∧ piece.origin.y < stock.bounds.y ∧
      piece.origin.z < stock.bounds.z := by
  unfold Fits AxisFits at h
  exact ⟨by omega, by omega, by omega⟩

theorem admitted_mem_choices {available : List Stock} {demand : Demand} {placement : Placement}
    (h : Admitted available demand placement) : placement ∈ choices available demand := by
  obtain ⟨stock, hstock, ⟨hname, hrotation⟩, hfits⟩ := h
  have hslot : placement.slot < available.length := List.getElem?_eq_some_iff.mp hstock |>.1
  obtain ⟨hx, hy, hz⟩ := admitted_in_bounds hfits
  obtain ⟨slot, ⟨name, origin, extent, rotation⟩⟩ := placement
  change name = demand.name at hname
  subst name
  let cell := (origin.x, origin.y, origin.z)
  have hc := Optimality.cell_in_stock stock (cell := cell) ⟨hx, hy, hz⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, List.mem_range.mpr hslot, ?_⟩
  change _ ∈ (match available[slot]? with | none => [] | some _ => _)
  simp only [hstock]
  apply List.mem_flatMap.mpr
  refine ⟨(rotation, extent), hrotation, List.mem_filterMap.mpr ⟨cell, hc, ?_⟩⟩
  have hpoint : Optimality.cellPoint cell = origin := by cases origin; rfl
  simp [hpoint, hfits]

inductive Assigns (available : List Stock) : List Demand → List Placement → Prop
  | nil : Assigns available [] []
  | cons : Admitted available next placement → Assigns available items rest →
      Assigns available (next :: items) (placement :: rest)

def anyPlan (available : List Stock) : List Demand → (List Placement → Bool) → Bool
  | [], accept => accept []
  | item :: rest, accept =>
    (choices available item).any (fun placement =>
      anyPlan available rest (fun plan => accept (placement :: plan)))

theorem detects_plan {available : List Stock} {items : List Demand} {plan : List Placement}
    (h : Assigns available items plan) (accept : List Placement → Bool)
    (haccept : accept plan = true) : anyPlan available items accept = true := by
  induction h generalizing accept with
  | nil => exact haccept
  | @cons item placement items plan hadmitted _ ih =>
    exact List.any_eq_true.mpr ⟨placement, admitted_mem_choices hadmitted,
      ih (fun rest => accept (placement :: rest)) haccept⟩

def Compatible (available : List Stock) (a b : Placement) : Prop :=
  match available[a.slot]? with
  | none => False
  | some stock => a.slot ≠ b.slot ∨ Separated stock.gap a.piece b.piece

instance (available : List Stock) : DecidableRel (Compatible available) := fun a b => by
  unfold Compatible
  split <;> infer_instance

def used (plan : List Placement) : Nat := (plan.map Placement.slot).eraseDups.length

def check (certificate : Certificate) : Bool :=
  let available := inventory certificate
  certificate.check && certificate.shortages.isEmpty &&
    !(anyPlan available (instances certificate) fun plan =>
      decide (plan.Pairwise (Compatible available) ∧ used plan < certificate.layoutCount))

/-- Every complete plan that can use fewer slots would be detected by the search. -/
theorem check_sound (certificate : Certificate) (h : check certificate = true) :
    certificate.Valid ∧ certificate.shortages = [] ∧
    ∀ plan, Assigns (inventory certificate) (instances certificate) plan →
      plan.Pairwise (Compatible (inventory certificate)) →
      certificate.layoutCount ≤ used plan := by
  simp only [check, Bool.and_eq_true, Certificate.check_iff, List.isEmpty_iff,
    Bool.not_eq_true', ← Bool.not_eq_true] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  intro plan hassign hpair
  apply Nat.le_of_not_gt
  intro hbetter
  exact h.2 (detects_plan hassign _ (decide_eq_true ⟨hpair, hbetter⟩))

def checkOutput (dimension : Dimension) (problem solution : Lean.Json) : Except String Bool := do
  let certificate ← readCertificate dimension problem solution
  unless certificate.check && certificate.shortages.isEmpty do return false
  let cuts := (certificate.demands.map Demand.quantity).sum
  unless 0 < cuts && cuts ≤ 64 && certificate.layouts.all (fun layout => !layout.pieces.isEmpty) do
    return false
  let volume := ((inventory certificate).map (Optimality.volume ∘ Stock.bounds)).sum
  unless volume ≤ 65_536 do return false
  let mut combinations := 1
  for demand in certificate.demands do
    combinations := combinations * (max 1 (volume * demand.orientations.length)) ^ demand.quantity
    unless combinations ≤ 65_536 do return false
  return check certificate

end Packing.ExactGrid
