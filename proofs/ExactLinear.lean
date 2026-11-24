import Optimality

set_option warningAsError true

namespace Packing.ExactLinear

open Lean

inductive Objective where
  | count
  | cost

structure Score where
  missing : Nat
  bars : Nat
  waste : Nat
  cost : Nat
  deriving DecidableEq

def Score.rank (score : Score) : Objective → List Nat
  | .count => [score.missing, score.bars, score.waste, score.cost]
  | .cost => [score.missing, score.cost, score.bars, score.waste]

structure Source where
  stock : Stock
  price : Nat

/-- Every used bar contains at least one cut, so no source can need more slots than cuts. -/
def slots (cuts : Nat) (sources : List Source) : List Source :=
  sources.flatMap (fun source => List.replicate (min cuts (source.stock.limit.getD cuts)) source)

def usage (tagged : List (Nat × Nat)) (slot : Source × Nat) : Option (Source × Nat) :=
  let lengths := (tagged.filter (fun cut => cut.2 == slot.2)).map Prod.fst
  if lengths.isEmpty then none else some (slot.1, linearLength slot.1.stock.gap lengths)

def evaluateTagged (available : List Source) (tagged : List (Nat × Nat)) : Option Score :=
  let used := (available.zipIdx 1).filterMap (usage tagged)
  if used.all (fun (source, length) => decide (length ≤ source.stock.bounds.x)) then
    some ⟨(tagged.map Prod.snd).count 0, used.length,
      (used.map (fun (source, length) => source.stock.bounds.x - length)).sum,
      (used.map (fun (source, _) => source.price)).sum⟩
  else none

/-- A cut assigned to zero is unplaced. Positive assignments address physical stock slots. -/
def evaluate (available : List Source) (cuts assignment : List Nat) : Option Score :=
  evaluateTagged available (cuts.zip assignment)

theorem evaluateTagged_perm (available : List Source) {left right : List (Nat × Nat)}
    (h : left.Perm right) : evaluateTagged available left = evaluateTagged available right := by
  have husage : usage left = usage right := by
    funext slot
    have hp := (h.filter (fun cut => cut.2 == slot.2)).map Prod.fst
    have hempty := hp.length_eq
    simp only [usage, List.isEmpty_iff_length_eq_zero, linearLength, hp.sum_nat, hempty]
  simp only [evaluateTagged, husage, (h.map Prod.snd).count_eq]

/-- Enumerate one choice per cut without materializing the product of choices. -/
def anyAssignment (choices : Nat) : Nat → (List Nat → Bool) → Bool
  | 0, accept => accept []
  | count + 1, accept =>
    (List.range choices).any (fun choice =>
      anyAssignment choices count (fun tail => accept (choice :: tail)))

theorem anyAssignment_iff (choices count : Nat) (accept : List Nat → Bool) :
    anyAssignment choices count accept = true ↔
      ∃ assignment : List Nat, assignment.length = count ∧
        (∀ slot ∈ assignment, slot < choices) ∧ accept assignment = true := by
  induction count generalizing accept with
  | zero => simp [anyAssignment]
  | succ count ih =>
    simp only [anyAssignment, List.any_eq_true, List.mem_range, ih]
    constructor
    · rintro ⟨choice, hchoice, tail, hlen, hslots, haccept⟩
      exact ⟨choice :: tail, by simp [hlen], by simpa [hchoice] using hslots, haccept⟩
    · rintro ⟨assignment, hlen, hslots, haccept⟩
      cases assignment with
      | nil => simp at hlen
      | cons choice tail =>
        exact ⟨choice, hslots choice (by simp), tail, by simpa using hlen,
          fun slot hm => hslots slot (List.mem_cons_of_mem _ hm), haccept⟩

def check (objective : Objective) (available : List Source) (cuts : List Nat)
    (candidate : Score) : Bool :=
  !(anyAssignment (available.length + 1) cuts.length (fun assignment =>
    (evaluate available cuts assignment).any (fun score =>
      (score.rank objective).lex (candidate.rank objective))))

def attainable (available : List Source) (cuts : List Nat) (candidate : Score) : Bool :=
  anyAssignment (available.length + 1) cuts.length (fun assignment =>
    decide (evaluate available cuts assignment = some candidate))

theorem attainable_iff (available : List Source) (cuts : List Nat) (candidate : Score) :
    attainable available cuts candidate = true ↔
      ∃ assignment : List Nat, assignment.length = cuts.length ∧
        (∀ slot ∈ assignment, slot < available.length + 1) ∧
        evaluate available cuts assignment = some candidate := by
  simp [attainable, anyAssignment_iff]

/-- Acceptance excludes every better feasible allocation, including allocations with shortages. -/
theorem check_iff (objective : Objective) (available : List Source) (cuts : List Nat)
    (candidate : Score) :
    check objective available cuts candidate = true ↔
      ∀ assignment : List Nat, assignment.length = cuts.length →
        (∀ slot ∈ assignment, slot < available.length + 1) →
        ∀ score, evaluate available cuts assignment = some score →
          ¬ List.Lex (· < ·) (score.rank objective) (candidate.rank objective) := by
  simp only [check, Bool.not_eq_true', ← Bool.not_eq_true, anyAssignment_iff]
  constructor
  · rintro h assignment hlen hslots score hscore hbetter
    apply h
    exact ⟨assignment, hlen, hslots, by simpa [hscore] using hbetter⟩
  · rintro h ⟨assignment, hlen, hslots, haccept⟩
    cases hscore : evaluate available cuts assignment with
    | none => simp [hscore] at haccept
    | some score => exact h assignment hlen hslots score hscore (by simpa [hscore] using haccept)

private theorem reorder {cuts : List Nat} {tagged : List (Nat × Nat)}
    (h : (tagged.map Prod.fst).Perm cuts) :
    ∃ assignment, assignment.length = cuts.length ∧ (cuts.zip assignment).Perm tagged := by
  induction cuts generalizing tagged with
  | nil =>
    have hnil : tagged = [] := by simpa using h.length_eq
    subst tagged
    exact ⟨[], rfl, .nil⟩
  | cons cut cuts ih =>
    obtain ⟨⟨length, slot⟩, hmem, heq⟩ :=
      List.mem_map.mp (h.mem_iff.mpr (List.mem_cons_self (a := cut) (l := cuts)))
    change length = cut at heq
    subst length
    have hp := List.perm_cons_erase hmem
    have htail : ((tagged.erase (cut, slot)).map Prod.fst).Perm cuts :=
      ((hp.symm.map Prod.fst).trans h).cons_inv
    obtain ⟨assignment, hlen, hzip⟩ := ih htail
    exact ⟨slot :: assignment, by simp [hlen], (hzip.cons (cut, slot)).trans hp.symm⟩

/-- A competing plan can group and order its cuts arbitrarily. The checker still covers it. -/
theorem excludes_better_plan (objective : Objective) (available : List Source) (cuts : List Nat)
    (candidate : Score) (hcheck : check objective available cuts candidate = true)
    (tagged : List (Nat × Nat)) (hcuts : (tagged.map Prod.fst).Perm cuts)
    (hslots : ∀ cut ∈ tagged, cut.2 < available.length + 1)
    (score : Score) (hscore : evaluateTagged available tagged = some score) :
    ¬ List.Lex (· < ·) (score.rank objective) (candidate.rank objective) := by
  obtain ⟨assignment, hlen, hzip⟩ := reorder hcuts
  have hle : assignment.length ≤ cuts.length := hlen ▸ Nat.le_refl _
  have hmap := List.map_snd_zip hle
  have hwithin : ∀ slot ∈ assignment, slot < available.length + 1 := by
    intro slot hm
    rw [← hmap] at hm
    obtain ⟨pair, hmem, rfl⟩ := List.mem_map.mp hm
    exact hslots pair (hzip.mem_iff.mp hmem)
  exact (check_iff objective available cuts candidate).mp hcheck assignment hlen hwithin score
    ((evaluateTagged_perm available hzip).trans hscore)

def checkOutput (objective : Objective) (problem solution : Json) : Except String Bool := do
  let certificate ← readCertificate .linear problem solution
  unless certificate.check do return false
  unless !certificate.stock.isEmpty && certificate.stock.all (fun stock =>
    decide (0 < stock.bounds.x ∧ stock.extent.x ≤ 2^30 ∧ stock.gap ≤ 2^30)) do return false
  unless !certificate.demands.isEmpty && certificate.demands.all (fun demand =>
    decide (0 < demand.extent.x ∧ demand.extent.x ≤ 2^30 ∧ 0 < demand.quantity)) do return false
  let cutCount := (certificate.demands.map Demand.quantity).sum
  unless cutCount ≤ 64 do return false
  let inputs ← problem.getObjValAs? (List Json) "stock"
  let sources ← (inputs.zip certificate.stock).mapM fun (input, stock) => do
    let price ← Optimality.exactPrice (← readDefault input "cost" (Json.num ⟨1, 0⟩))
    return Source.mk stock price
  let available := slots cutCount sources
  unless (available.length + 1) ^ cutCount ≤ 65_536 do return false
  -- All competing totals must use exactly representable arithmetic as well.
  unless (available.map Source.price).sum ≤ 2^53 do return false
  let layoutInputs ← solution.getObjValAs? (List Json) "layouts"
  let mut candidate : Score := ⟨(certificate.shortages.map Shortage.quantity).sum,
    certificate.layoutCount, 0, 0⟩
  for (layout, raw) in certificate.layouts.zip layoutInputs do
    let some source := sources.find? (fun source => source.stock.name == layout.stock)
      | throw "unknown priced stock"
    let some summary := layout.linear | throw "missing linear layout totals"
    let price ← Optimality.exactPrice (← raw.getObjVal? "cost")
    unless !layout.pieces.isEmpty && price == source.price do return false
    candidate := { candidate with
      waste := candidate.waste + summary.waste
      cost := candidate.cost + source.price }
  let waste ← solution.getObjValAs? Nat "total_waste"
  let cost ← Optimality.exactPrice (← solution.getObjVal? "total_cost")
  return waste == candidate.waste && cost == candidate.cost &&
    attainable available (Optimality.requiredLengths certificate) candidate &&
    check objective available (Optimality.requiredLengths certificate) candidate

end Packing.ExactLinear
