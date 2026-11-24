import Packing

set_option warningAsError true

namespace Packing.Optimality

open Lean

def paddedLoad (kerf : Nat) (cuts : List Nat) : Nat :=
  (cuts.map (fun length => length + kerf)).sum

theorem paddedLoad_eq (kerf : Nat) (cuts : List Nat) :
    paddedLoad kerf cuts = cuts.sum + kerf * cuts.length := by
  induction cuts with
  | nil => simp [paddedLoad]
  | cons head tail ih =>
    simp only [paddedLoad, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at *
    omega

theorem paddedLoad_fits (kerf capacity : Nat) (cuts : List Nat)
    (h : linearLength kerf cuts ≤ capacity) : paddedLoad kerf cuts ≤ capacity + kerf := by
  rw [paddedLoad_eq]
  cases cuts with
  | nil => simp
  | cons head tail =>
    simp only [linearLength, List.sum_cons, List.length_cons, Nat.add_sub_cancel,
      Nat.mul_succ] at *
    omega

theorem total_load_le (capacity : Nat) (loads : List Nat)
    (h : ∀ load ∈ loads, load ≤ capacity) : loads.sum ≤ capacity * loads.length := by
  induction loads with
  | nil => simp
  | cons head rest ih =>
    have hhead := h head (by simp)
    have htail := ih (fun load hm => h load (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem lower_bound_for_load {capacity total count : Nat}
    (threshold : capacity * count < total) (loads : List Nat)
    (sameTotal : loads.sum = total) (fits : ∀ load ∈ loads, load ≤ capacity) :
    count < loads.length := by
  apply Classical.byContradiction
  intro h
  have hcount : loads.length ≤ count := by omega
  have hcapacity := Nat.mul_le_mul_left capacity hcount
  have hsum := total_load_le capacity loads fits
  omega

def paddedTotal (kerf : Nat) (bins : List (List Nat)) : Nat :=
  (bins.map (paddedLoad kerf)).sum

theorem paddedTotal_eq (kerf : Nat) (bins : List (List Nat)) :
    paddedTotal kerf bins = paddedLoad kerf bins.flatten := by
  induction bins with
  | nil => rfl
  | cons head tail ih =>
    simp only [paddedTotal, List.map_cons, List.sum_cons] at *
    rw [ih]
    simp [paddedLoad, List.map_append, List.sum_append]

/-- Any complete grouping that passes the physical cut length rule needs at least `count` bars. -/
theorem linear_lower_bound {kerf capacity total count : Nat}
    (threshold : count = 0 ∨ (capacity + kerf) * (count - 1) < total)
    (bins : List (List Nat)) (sameTotal : paddedLoad kerf bins.flatten = total)
    (fits : ∀ cuts ∈ bins, linearLength kerf cuts ≤ capacity) :
    count ≤ bins.length := by
  rcases threshold with hzero | hloads
  · simp [hzero]
  · have h := lower_bound_for_load hloads (bins.map (paddedLoad kerf))
      (by exact (paddedTotal_eq kerf bins).trans sameTotal)
      (by
        intro load hm
        obtain ⟨cuts, hmem, rfl⟩ := List.mem_map.mp hm
        exact paddedLoad_fits _ _ cuts (fits cuts hmem))
    simp only [List.length_map] at h
    omega

def requiredLengths (certificate : Certificate) : List Nat :=
  certificate.demands.flatMap (fun demand => List.replicate demand.quantity demand.extent.x)

private theorem sum_eq_of_perm {left right : List Nat} (h : left.Perm right) :
    left.sum = right.sum := by
  induction h <;> simp_all [Nat.add_left_comm]

/-- Certify attainment of the padded-load bound for a single source stock type. -/
def checkOptimalLinear (certificate : Certificate) : Bool :=
  match certificate.stock with
  | [stock] =>
    let total := paddedLoad stock.gap (requiredLengths certificate)
    certificate.check && certificate.shortages.isEmpty &&
      decide (certificate.layoutCount = 0 ∨
        (stock.bounds.x + stock.gap) * (certificate.layoutCount - 1) < total)
  | _ => false

/-- Every grouping of the full cut list that fits the stock uses at least as many bars. -/
theorem checkOptimalLinear_sound (certificate : Certificate) (stock : Stock)
    (hstock : certificate.stock = [stock]) (hcheck : checkOptimalLinear certificate = true) :
    certificate.Valid ∧
    ∀ bins : List (List Nat), bins.flatten.Perm (requiredLengths certificate) →
      (∀ cuts ∈ bins, linearLength stock.gap cuts ≤ stock.bounds.x) →
      certificate.layoutCount ≤ bins.length := by
  simp only [checkOptimalLinear, hstock, Bool.and_eq_true, Certificate.check_iff,
    decide_eq_true_eq] at hcheck
  refine ⟨hcheck.1.1, ?_⟩
  intro bins sameCuts fits
  exact linear_lower_bound hcheck.2 bins
    (sum_eq_of_perm (sameCuts.map (fun length => length + stock.gap))) fits

def checkOptimalLinearOutput (problem solution : Json) : Except String Bool := do
  let certificate ← readCertificate .linear problem solution
  return checkOptimalLinear certificate

def cartesian (left : List α) (right : List β) : List (α × β) :=
  left.flatMap (fun a => right.map (fun b => (a, b)))

@[simp] theorem cartesian_length (left : List α) (right : List β) :
    (cartesian left right).length = left.length * right.length := by
  induction left with
  | nil => simp [cartesian]
  | cons head tail ih =>
    simpa [cartesian, Nat.succ_mul, Nat.add_comm] using
      congrArg (right.length + ·) ih

@[simp] theorem mem_cartesian {left : List α} {right : List β} {p : α × β} :
    p ∈ cartesian left right ↔ p.1 ∈ left ∧ p.2 ∈ right := by
  cases p
  constructor
  · intro h
    obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
    cases heq
    exact ⟨ha, hb⟩
  · intro ⟨ha, hb⟩
    exact List.mem_flatMap.mpr ⟨_, ha, List.mem_map.mpr ⟨_, hb, rfl⟩⟩

theorem cartesian_nodup {left : List α} {right : List β}
    (hl : left.Nodup) (hr : right.Nodup) : (cartesian left right).Nodup := by
  simp only [cartesian, List.nodup_iff_pairwise_ne, List.pairwise_flatMap, List.pairwise_map]
  constructor
  · intro a _
    exact hr.imp (fun hn heq => hn (congrArg Prod.snd heq))
  · apply hl.imp
    intro a b hne p hp q hq heq
    obtain ⟨first, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨second, _, rfl⟩ := List.mem_map.mp hq
    exact hne (congrArg Prod.fst heq)

def cells (origin extent : Axes) : List (Nat × Nat × Nat) :=
  cartesian (List.range' origin.x extent.x)
    (cartesian (List.range' origin.y extent.y) (List.range' origin.z extent.z))

def volume (extent : Axes) : Nat := extent.x * extent.y * extent.z

theorem cells_length (origin extent : Axes) : (cells origin extent).length = volume extent := by
  simp [cells, volume, Nat.mul_assoc]

theorem cells_nodup (origin extent : Axes) : (cells origin extent).Nodup :=
  cartesian_nodup (List.nodup_range' 1)
    (cartesian_nodup (List.nodup_range' 1) (List.nodup_range' 1))

def cellPoint (cell : Nat × Nat × Nat) : Axes := ⟨cell.1, cell.2.1, cell.2.2⟩

theorem occupies_cells (piece : Piece) (cell : Nat × Nat × Nat) :
    cell ∈ cells piece.origin piece.extent ↔ Occupies piece (cellPoint cell) := by
  simp [cells, cellPoint, Occupies, ClearanceCell, and_assoc]

theorem cell_in_stock (stock : Stock) (cell : Nat × Nat × Nat)
    (h : cell.1 < stock.bounds.x ∧ cell.2.1 < stock.bounds.y ∧ cell.2.2 < stock.bounds.z) :
    cell ∈ cells ⟨0, 0, 0⟩ stock.bounds := by
  simpa [cells] using h

theorem occupies_has_clearance {piece : Piece} {cell : Axes} {gap : Nat}
    (h : Occupies piece cell) : ClearanceCell gap piece cell := by
  unfold Occupies ClearanceCell at *
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

def usedVolume (layout : Layout) : Nat := (layout.pieces.map (volume ∘ Piece.extent)).sum

theorem length_occupied_cells (pieces : List Piece) :
    (pieces.flatMap (fun piece => cells piece.origin piece.extent)).length =
      (pieces.map (volume ∘ Piece.extent)).sum := by
  simp [List.length_flatMap, cells_length, Function.comp_def]

/-- The stock's finite grid bounds the sum of the sizes of all distinct occupied cells. -/
theorem layout_volume_fits (stock : Stock) (layout : Layout) (h : layout.Valid stock) :
    usedVolume layout ≤ volume stock.bounds := by
  let occupied := layout.pieces.flatMap (fun piece => cells piece.origin piece.extent)
  obtain ⟨bounds, disjoint⟩ := Layout.physical h
  have unique : occupied.Nodup := by
    apply List.pairwise_flatMap.mpr
    refine ⟨fun piece _ => cells_nodup piece.origin piece.extent, disjoint.imp ?_⟩
    intro a b hab cell ha same hb heq
    subst same
    exact hab (cellPoint cell) (occupies_has_clearance ((occupies_cells a cell).mp ha))
      (occupies_has_clearance ((occupies_cells b cell).mp hb))
  have subset : occupied ⊆ cells ⟨0, 0, 0⟩ stock.bounds := by
    intro cell hmem
    obtain ⟨part, placed, inside⟩ := List.mem_flatMap.mp hmem
    exact cell_in_stock stock cell (bounds part placed (cellPoint cell) ((occupies_cells part cell).mp inside))
  have sized := unique.length_le_of_subset subset
  change (layout.pieces.flatMap _).length ≤ _ at sized
  rwa [length_occupied_cells, cells_length] at sized

def requiredVolumes (certificate : Certificate) : List Nat :=
  certificate.demands.flatMap (fun demand => List.replicate demand.quantity (volume demand.extent))

def checkOptimalRectangular (certificate : Certificate) : Bool :=
  match certificate.stock with
  | [stock] =>
    certificate.check && certificate.shortages.isEmpty &&
      decide (certificate.layoutCount = 0 ∨
        volume stock.bounds * (certificate.layoutCount - 1) < (requiredVolumes certificate).sum)
  | _ => false

theorem lengths_sum_of_flatMap (layouts : List Layout) :
    (layouts.flatMap (fun layout => layout.pieces.map (volume ∘ Piece.extent))).sum =
      (layouts.map usedVolume).sum := by
  induction layouts with
  | nil => rfl
  | cons head tail ih => simp [ih, usedVolume, List.sum_append]

/-- A matching area or volume bound excludes all complete one-stock packings with fewer layouts. -/
theorem checkOptimalRectangular_sound (certificate : Certificate) (stock : Stock)
    (hstock : certificate.stock = [stock]) (hcheck : checkOptimalRectangular certificate = true) :
    certificate.Valid ∧ ∀ layouts : List Layout,
      (∀ layout ∈ layouts, layout.Valid stock) →
      (layouts.flatMap (fun layout => layout.pieces.map (volume ∘ Piece.extent))).Perm
        (requiredVolumes certificate) →
      certificate.layoutCount ≤ layouts.length := by
  simp only [checkOptimalRectangular, hstock, Bool.and_eq_true, Certificate.check_iff,
    decide_eq_true_eq] at hcheck
  refine ⟨hcheck.1.1, ?_⟩
  intro layouts valid sameVolumes
  rcases hcheck.2 with hzero | hthreshold
  · simp [hzero]
  · have htotal := sum_eq_of_perm sameVolumes
    rw [lengths_sum_of_flatMap] at htotal
    have h := lower_bound_for_load hthreshold (layouts.map usedVolume) htotal (by
      intro load hm
      obtain ⟨layout, hmem, rfl⟩ := List.mem_map.mp hm
      exact layout_volume_fits stock layout (valid layout hmem))
    simp only [List.length_map] at h
    omega

def checkOptimalRectangularOutput (dim : Dimension) (problem solution : Json) : Except String Bool := do
  let certificate ← readCertificate dim problem solution
  return checkOptimalRectangular certificate

structure PricedStock where
  usable : Nat
  price : Nat

def planPrice (bars : List (PricedStock × List Nat)) : Nat :=
  (bars.map (fun (stock, _) => stock.price)).sum

def checkCostBound (stocks : List PricedStock) (lengths : List Nat) (candidate : Nat) : Bool :=
  candidate == 0 || stocks.any (fun reference =>
    decide (0 < reference.usable ∧ reference.usable * (candidate - 1) < reference.price * lengths.sum) &&
    stocks.all (fun stock => decide (reference.price * stock.usable ≤ reference.usable * stock.price)))

theorem weighted_load_le_price (reference : PricedStock) (stocks : List PricedStock)
    (pricing : ∀ stock ∈ stocks, reference.price * stock.usable ≤ reference.usable * stock.price)
    (bars : List (PricedStock × List Nat))
    (fits : ∀ (bar : PricedStock × List Nat), bar ∈ bars → bar.1 ∈ stocks ∧ bar.2.sum ≤ bar.1.usable) :
    reference.price * (bars.flatMap Prod.snd).sum ≤ reference.usable * planPrice bars := by
  induction bars with
  | nil => simp [planPrice]
  | cons head rest ih =>
    obtain ⟨hmem, hcapacity⟩ := fits head (by simp)
    have hhead := Nat.le_trans (Nat.mul_le_mul_left reference.price hcapacity) (pricing _ hmem)
    have hrest := ih (fun bar hm => fits bar (by simp [hm]))
    simp only [planPrice, List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons,
      Nat.mul_add] at *
    omega

/-- A tight material-price bound excludes every full packing with a cheaper exact price. -/
theorem checkCostBound_sound (stocks : List PricedStock) (lengths : List Nat) (candidate : Nat)
    (checked : checkCostBound stocks lengths candidate = true)
    (bars : List (PricedStock × List Nat))
    (sameCuts : (bars.flatMap Prod.snd).Perm lengths)
    (fits : ∀ (bar : PricedStock × List Nat), bar ∈ bars → bar.1 ∈ stocks ∧ bar.2.sum ≤ bar.1.usable) :
    candidate ≤ planPrice bars := by
  simp only [checkCostBound, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at checked
  rcases checked with hzero | ⟨reference, _, ⟨_, htight⟩, pricing⟩
  · simp [hzero]
  · have h := weighted_load_le_price reference stocks pricing bars fits
    rw [sum_eq_of_perm sameCuts] at h
    apply Classical.byContradiction
    intro hcheaper
    have hcost : planPrice bars ≤ candidate - 1 := by omega
    have hscale := Nat.mul_le_mul_left reference.usable hcost
    omega

/-- Widening the 1D model from physical cut use to bare demand lengths preserves the lower bound. -/
theorem bare_cuts_fit {kerf capacity : Nat} {lengths : List Nat}
    (h : linearLength kerf lengths ≤ capacity) : lengths.sum ≤ capacity := by
  unfold linearLength at h
  omega

def exactPrice (value : Json) : Except String Nat := do
  let number ← value.getNum?
  unless number.exponent ≤ 350 do throw "stock price exceeds supported decimal precision"
  let units := 10 ^ number.exponent
  let mantissa := number.mantissa.natAbs
  let amount := mantissa / units
  unless 0 ≤ number.mantissa && mantissa % units == 0 && amount ≤ 2^53 do
    throw "cost bound requires nonnegative exact integral stock prices and totals"
  return amount

def checkMinimumLinearCost (problem solution : Json) : Except String Bool := do
  let certificate ← readCertificate .linear problem solution
  unless certificate.check && certificate.shortages.isEmpty do return false
  let inputs ← problem.getObjValAs? (List Json) "stock"
  let prices ← (inputs.zip certificate.stock).mapM fun (input, stock) => do
    let price ← exactPrice (← readDefault input "cost" (Json.num ⟨1, 0⟩))
    return (stock.name, PricedStock.mk stock.bounds.x price)
  let mut actual := 0
  let layouts ← solution.getObjValAs? (List Json) "layouts"
  for (layout, raw) in certificate.layouts.zip layouts do
    let some (_, source) := prices.find? (fun (name, _) => name == layout.stock)
      | throw "unknown priced stock"
    let reported ← exactPrice (← raw.getObjVal? "cost")
    unless reported == source.price do return false
    actual := actual + source.price
  let total ← exactPrice (← solution.getObjVal? "total_cost")
  return total == actual && checkCostBound (prices.map Prod.snd) (requiredLengths certificate) total

end Packing.Optimality
