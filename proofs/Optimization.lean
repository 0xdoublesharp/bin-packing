import ExactLinear
import ExactGrid
import Staged
import Loading

set_option warningAsError true

namespace Packing.Optimization

open Lean
open Optimality (volume)

inductive PackingObjective where
  | bin_count | total_cost | knapsack | feasibility
  | open_dimension_x | open_dimension_y | open_dimension_z | open_dimension_xy
  deriving DecidableEq, FromJson

def PackingObjective.axes : PackingObjective → List Nat
  | .open_dimension_x => [0]
  | .open_dimension_y => [1]
  | .open_dimension_z => [2]
  | .open_dimension_xy => [0, 1]
  | _ => []

def extentValue (objective : PackingObjective) (size : Axes) : Nat :=
  match objective with
  | .open_dimension_x => size.x
  | .open_dimension_y => size.y
  | .open_dimension_z => size.z
  | .open_dimension_xy => size.x * size.y
  | _ => 1

def fixedExtent (objective : PackingObjective) (size : Axes) : Nat :=
  match objective with
  | .open_dimension_x => size.y * size.z
  | .open_dimension_y => size.x * size.z
  | .open_dimension_z => size.x * size.y
  | .open_dimension_xy => size.z
  | _ => volume size

structure OptScore where
  missingRequested : Nat
  missingMinima : Nat
  profit : Nat
  containers : Nat
  cost : Nat
  waste : Nat
  extent : Axes
  deriving DecidableEq, Repr

def OptScore.rank (score : OptScore) (objective : PackingObjective) (maxProfit : Nat) : List Nat :=
  let primary := match objective with
    | .knapsack => maxProfit - score.profit
    | .total_cost => score.cost
    | .bin_count | .feasibility => score.containers
    | _ => extentValue objective score.extent
  [if objective == .knapsack then score.missingMinima else score.missingRequested,
    primary, score.containers, score.cost, score.waste]

def Better (objective : PackingObjective) (maxProfit : Nat) (a b : OptScore) : Prop :=
  List.Lex (· < ·) (a.rank objective maxProfit) (b.rank objective maxProfit)

theorem rank_irrefl (objective : PackingObjective) (maxProfit : Nat) (score : OptScore) :
    ¬ Better objective maxProfit score score :=
  List.lex_irrefl Nat.lt_irrefl _

theorem rank_trans {objective : PackingObjective} {maxProfit : Nat} {a b c : OptScore}
    (hab : Better objective maxProfit a b) (hbc : Better objective maxProfit b c) :
    Better objective maxProfit a c :=
  List.lex_trans Nat.lt_trans hab hbc

theorem rank_tie (objective : PackingObjective) (maxProfit : Nat) (a b : OptScore)
    (hab : ¬ Better objective maxProfit a b) (hba : ¬ Better objective maxProfit b a) :
    a.rank objective maxProfit = b.rank objective maxProfit :=
  List.lex_trichotomous (r := (· < ·)) (fun _ _ hxy hyx =>
    Nat.le_antisymm (Nat.le_of_not_gt hyx) (Nat.le_of_not_gt hxy)) hba hab

theorem profit_rank_reverses {maximum a b : Nat} (ha : a ≤ maximum) (hb : b ≤ maximum) :
    maximum - a < maximum - b ↔ b < a := by omega

/-- Prices and profits are measured in units of 2⁻¹⁶. -/
def dyadicScale : Nat := 2 ^ 16

private def maxExactUnits : Nat := 2 ^ 53

private def exactAmountError : String :=
  "exact binary64 certificate requires nonnegative dyadic amounts with denominator dividing 2^16 and totals at most 2^53 / 2^16"

private def stripDecimalZeros (mantissa : Nat) : Nat → Nat × Nat
  | 0 => (mantissa, 0)
  | exponent + 1 =>
    if mantissa % 10 == 0 then stripDecimalZeros (mantissa / 10) exponent
    else (mantissa, exponent + 1)

private def readAmount (value : Json) : Except String Nat := do
  let number ← value.getNum?
  unless 0 ≤ number.mantissa do throw exactAmountError
  if number.mantissa == 0 then return 0
  let (mantissa, exponent) := stripDecimalZeros number.mantissa.natAbs number.exponent
  unless exponent ≤ 16 do throw exactAmountError
  let factor := 5 ^ exponent
  unless mantissa % factor == 0 do throw exactAmountError
  let units := (mantissa / factor) * 2 ^ (16 - exponent)
  unless units ≤ maxExactUnits do throw exactAmountError
  return units

example : (readAmount (.num ⟨1, 1⟩)).isOk = false := by decide
example : (readAmount (.num ⟨175000000000000000, 17⟩)).toOption = some (7 * 2 ^ 14) := by decide
example : (readAmount (.num ⟨152587890625, 16⟩)).toOption = some 1 := by decide
example : (readAmount (.num ⟨2 ^ 37, 0⟩)).toOption = some maxExactUnits := by decide
example : (readAmount (.num ⟨2 ^ 37 + 1, 0⟩)).isOk = false := by decide

structure DemandRow where
  demand : Demand
  profit : Nat
  minimum : Nat
  weight : Nat := 0

structure StockRow where
  stock : Stock
  cost : Nat
  sheet : Indexed.SheetRules := {}
  payload : Option Nat := none

/-- The first component distinguishes source rows even when all their wire fields match. -/
def copies (rows : List DemandRow) : List (Nat × DemandRow) :=
  rows.zipIdx.flatMap fun (row, index) => List.replicate row.demand.quantity (index, row)

private def stockMultiplicity (cap : Nat) (row : StockRow) : Nat :=
  min cap (row.stock.limit.getD cap)

/-- Each usable container has at least one copy, so no stock type needs more slots than copies. -/
def slots (rows : List DemandRow) (stock : List StockRow) : List StockRow :=
  let cap := (rows.map (·.demand.quantity)).sum
  stock.flatMap fun row => List.replicate (stockMultiplicity cap row) row

def profitOf (quantities : List Nat) (profits : List Nat) : Nat :=
  ((quantities.zip profits).map fun (quantity, profit) => quantity * profit).sum

def maxProfit (rows : List DemandRow) : Nat :=
  (rows.map (fun row => row.demand.quantity * row.profit)).sum

private def selectedProfit (rows : List DemandRow) (placed : List Nat) : Nat :=
  (rows.zipIdx.map fun (row, index) => placed.count index * row.profit).sum

def deficit (requirements counts : List Nat) : Nat :=
  ((requirements.zip counts).map fun (required, placed) => required - placed).sum

def scoreFor (rows : List DemandRow) (placed : List Nat) (containers cost waste : Nat)
    (extent : Axes := ⟨0, 0, 0⟩) : OptScore :=
  let selected := rows.zipIdx.map fun (_, index) => placed.count index
  ⟨deficit (rows.map (·.demand.quantity)) selected, deficit (rows.map DemandRow.minimum) selected,
    selectedProfit rows placed, containers, cost, waste, extent⟩

private theorem sumWeight_le (entries : List α) (first second : α → Nat)
    (le : ∀ entry ∈ entries, first entry ≤ second entry) :
    (entries.map first).sum ≤ (entries.map second).sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    exact Nat.add_le_add (le _ (by simp)) (ih (fun e hm => le _ (by simp [hm])))

private def copyIndices (rows : List DemandRow) (start : Nat) : List Nat :=
  (rows.zipIdx start).flatMap fun (row, index) => List.replicate row.demand.quantity index

private theorem count_copies {rows : List DemandRow} {row : DemandRow} {start index : Nat}
    (source : (row, index) ∈ rows.zipIdx start) : (copyIndices rows start).count index = row.demand.quantity := by
  induction rows generalizing start with
  | nil => simp at source
  | cons head tail ih =>
    simp only [List.zipIdx_cons, List.mem_cons] at source
    change (List.replicate head.demand.quantity start ++ copyIndices tail (start + 1)).count index = _
    rw [List.count_append]
    rcases source with h | h
    · cases h
      have absent : index ∉ copyIndices tail (index + 1) := by
        intro hm
        obtain ⟨⟨_, j⟩, hsource, hcopy⟩ := List.mem_flatMap.mp hm
        have heq : index = j := List.eq_of_mem_replicate hcopy
        have hj : index + 1 ≤ j := List.le_snd_of_mem_zipIdx hsource
        omega
      simp [List.count_eq_zero_of_not_mem absent]
    · have hindex : start + 1 ≤ index := List.le_snd_of_mem_zipIdx h
      have hne : start ≠ index := by omega
      simp [List.count_replicate, hne, ih h]

private theorem selectedProfit_le (rows : List DemandRow) (placed : List Nat)
    (h : List.Sublist placed ((copies rows).map Prod.fst)) : selectedProfit rows placed ≤ maxProfit rows := by
  have hcopies : (copies rows).map Prod.fst = copyIndices rows 0 := by
    simp [copies, copyIndices, List.map_flatMap]
  rw [hcopies] at h
  have hmax : maxProfit rows = (rows.zipIdx.map (fun (row, _) => row.demand.quantity * row.profit)).sum := by
    have hmap := congrArg (fun sources : List DemandRow =>
      (sources.map (fun row => row.demand.quantity * row.profit)).sum) (List.zipIdx_map_fst 0 rows)
    simpa only [maxProfit, List.map_map, Function.comp_def] using hmap.symm
  rw [selectedProfit, hmax]
  apply sumWeight_le
  intro source hs
  have hc := h.count_le source.2
  rw [count_copies hs] at hc
  exact Nat.mul_le_mul_right _ hc

theorem better_of_higher_profit {maximum : Nat} {a b : OptScore}
    (amin : a.missingMinima = b.missingMinima) (ha : a.profit ≤ maximum) (hb : b.profit ≤ maximum)
    (higher : b.profit < a.profit) : Better .knapsack maximum a b := by
  unfold Better OptScore.rank
  simp only [beq_self_eq_true, ite_true]
  rw [amin]
  exact .cons (.rel ((profit_rank_reverses ha hb).mpr higher))

private theorem zipFirst_sublist (items : List α) (plan : List β) :
    List.Sublist ((items.zip plan).map Prod.fst) items := by
  induction items generalizing plan with
  | nil => simp
  | cons item rest ih =>
    cases plan with
    | nil => simp
    | cons slot remaining => exact .cons_cons item (ih remaining)

/-- A plan chooses one admissible alternative for each copy, in source order. -/
inductive Chooses (α : Type) : List (List α) → List α → Prop
  | nil : Chooses α [] []
  | cons : choice ∈ choices → Chooses α rest plan →
      Chooses α (choices :: rest) (choice :: plan)

def anyChoices : List (List α) → (List α → Bool) → Bool
  | [], accept => accept []
  | choices :: rest, accept => choices.any fun choice =>
      anyChoices rest (fun plan => accept (choice :: plan))

theorem anyChoices_iff (choices : List (List α)) (accept : List α → Bool) :
    anyChoices choices accept = true ↔ ∃ plan, Chooses α choices plan ∧ accept plan = true := by
  induction choices generalizing accept with
  | nil =>
    simp only [anyChoices]
    exact ⟨fun h => ⟨[], .nil, h⟩, by rintro ⟨_, h, hp⟩; cases h; exact hp⟩
  | cons choices rest ih =>
    simp only [anyChoices, List.any_eq_true, ih]
    constructor
    · rintro ⟨choice, hm, plan, hp, ha⟩
      exact ⟨choice :: plan, .cons hm hp, ha⟩
    · rintro ⟨_, h, ha⟩
      cases h with
      | cons hm hp => exact ⟨_, hm, _, hp, ha⟩

private def searchBudget (choiceCounts : List Nat) : Bool :=
  choiceCounts.length ≤ 128 && (choiceCounts.map (max 1)).prod ≤ 65_536

private def slotGroups (available : List StockRow) (entries : List α) (key : α → Nat)
    (start : Nat := 0) : List (StockRow × List α) :=
  (available.zipIdx start).map fun (row, index) => (row, entries.filter (fun entry => key entry == index))

private def linearLengths (entries : List ((Nat × DemandRow) × Nat)) : List Nat :=
  entries.map (·.1.2.demand.extent.x)

private def linearFits (row : StockRow) (entries : List ((Nat × DemandRow) × Nat)) : Bool :=
  linearLength row.stock.gap (linearLengths entries) ≤ row.stock.bounds.x

private def linearTagged (rows : List DemandRow) (plan : List Nat) : List ((Nat × DemandRow) × Nat) :=
  (copies rows).zip plan

private def linearChoices (rows : List DemandRow) (available : List StockRow) : List (List Nat) :=
  (copies rows).map fun _ => List.range (available.length + 1)

/-- Zero skips a copy. The remaining choices address physical stock slots starting at one. -/
def LinearPlan (rows : List DemandRow) (available : List StockRow) (plan : List Nat) : Prop :=
  Chooses Nat (linearChoices rows available) plan

def evaluateLinear (rows : List DemandRow) (available : List StockRow) (plan : List Nat) :
    Option OptScore :=
  let tagged := linearTagged rows plan
  let used := (slotGroups available tagged Prod.snd 1).filter (fun (_, entries) => !entries.isEmpty)
  if used.all (fun (row, entries) => linearFits row entries) then
    let placed := (tagged.filter fun (_, slot) => slot != 0).map (·.1.1)
    some (scoreFor rows placed used.length (used.map (·.1.cost)).sum
      ((used.map fun (row, entries) => row.stock.bounds.x -
        linearLength row.stock.gap (linearLengths entries)).sum))
  else none

theorem evaluateLinear_profit {rows : List DemandRow} {available : List StockRow} {plan : List Nat}
    {score : OptScore} (h : evaluateLinear rows available plan = some score) : score.profit ≤ maxProfit rows := by
  simp only [evaluateLinear] at h
  split at h
  next =>
    cases Option.some.inj h
    have hsub := (List.filter_sublist (l := linearTagged rows plan)
      (p := fun (_, slot) => slot != 0)).map (fun entry => entry.1.1)
    have hzip := (zipFirst_sublist (copies rows) plan).map Prod.fst
    simp only [List.map_map, Function.comp_def] at hzip
    exact selectedProfit_le rows _ (hsub.trans hzip)
  next => contradiction

private def anyLinear (rows : List DemandRow) (available : List StockRow)
    (accept : OptScore → Bool) : Bool :=
  anyChoices (linearChoices rows available) fun plan => (evaluateLinear rows available plan).any accept

theorem anyLinear_iff (rows : List DemandRow) (available : List StockRow) (accept : OptScore → Bool) :
    anyLinear rows available accept = true ↔ ∃ plan score,
      LinearPlan rows available plan ∧ evaluateLinear rows available plan = some score ∧
        accept score = true := by
  simp only [anyLinear, anyChoices_iff, LinearPlan]
  constructor
  · rintro ⟨plan, hp, h⟩
    cases hs : evaluateLinear rows available plan with
    | none => simp [hs] at h
    | some score => exact ⟨plan, score, hp, hs, by simpa [hs] using h⟩
  · rintro ⟨plan, score, hp, hs, h⟩
    exact ⟨plan, hp, by simpa [hs] using h⟩

private def cheaperRank (rows : List DemandRow) (objective : PackingObjective) (candidate score : OptScore) : Bool :=
  (score.rank objective (maxProfit rows)).lex (candidate.rank objective (maxProfit rows))

/-- Certify that the given minimum-satisfying knapsack score is attained and rank-optimal. -/
def checkExactKnapsack1D (rows : List DemandRow) (stock : List StockRow) (candidate : OptScore) : Bool :=
  let available := slots rows stock
  searchBudget (List.replicate (copies rows).length (available.length + 1)) &&
    candidate.missingMinima == 0 &&
    anyLinear rows available (· == candidate) &&
    !anyLinear rows available (cheaperRank rows .knapsack candidate)

theorem exactKnapsack1D_sound (rows : List DemandRow) (stock : List StockRow) (candidate : OptScore)
    (h : checkExactKnapsack1D rows stock candidate = true) :
    candidate.missingMinima = 0 ∧
    (∃ plan, LinearPlan rows (slots rows stock) plan ∧
      evaluateLinear rows (slots rows stock) plan = some candidate) ∧
    ∀ plan score, LinearPlan rows (slots rows stock) plan →
      evaluateLinear rows (slots rows stock) plan = some score →
      (¬ Better .knapsack (maxProfit rows) score candidate) ∧
      (score.missingMinima = 0 → score.profit ≤ candidate.profit) := by
  simp only [checkExactKnapsack1D, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    ← Bool.not_eq_true, anyLinear_iff] at h
  obtain ⟨⟨⟨_, hmin⟩, plan, score, hp, hs, heq⟩, hbetter⟩ := h
  subst score
  refine ⟨hmin, ⟨plan, hp, hs⟩, fun q s hq he => ?_⟩
  have excludes : ¬ Better .knapsack (maxProfit rows) s candidate := fun hb =>
    hbetter ⟨q, s, hq, he, by simpa [cheaperRank, Better] using hb⟩
  refine ⟨excludes, fun hzero => Nat.le_of_not_gt (fun higher => excludes ?_)⟩
  exact better_of_higher_profit (hzero.trans hmin.symm) (evaluateLinear_profit he)
    (evaluateLinear_profit hs) higher

private def gridChoices (rows : List DemandRow) (available : List StockRow) :
    List (List (Option ExactGrid.Placement)) :=
  (copies rows).map fun (_, row) => none ::
    (ExactGrid.choices (available.map StockRow.stock) row.demand).map some

/-- A grid plan assigns each source copy to an integer placement or omits it. -/
inductive GridPlan (available : List StockRow) : List (Nat × DemandRow) →
    List (Option ExactGrid.Placement) → Prop
  | nil : GridPlan available [] []
  | skip : GridPlan available rest plan → GridPlan available (item :: rest) (none :: plan)
  | place : ExactGrid.Admitted (available.map StockRow.stock) item.2.demand placement →
      GridPlan available rest plan → GridPlan available (item :: rest) (some placement :: plan)

theorem gridPlan_covered {items : List (Nat × DemandRow)} {available : List StockRow}
    {plan : List (Option ExactGrid.Placement)} (h : GridPlan available items plan) :
    Chooses (Option ExactGrid.Placement)
      (items.map fun (_, row) => none :: (ExactGrid.choices (available.map StockRow.stock) row.demand).map some)
      plan := by
  induction h with
  | nil => exact .nil
  | skip _ ih => exact .cons (by simp) ih
  | place ha _ ih => exact .cons (by simp [ExactGrid.admitted_mem_choices ha]) ih

private def gridTagged (items : List (Nat × DemandRow)) (plan : List (Option ExactGrid.Placement)) :
    List ((Nat × DemandRow) × ExactGrid.Placement) :=
  (items.zip plan).filterMap fun (item, placement) => placement.map (item, ·)

private def gridLayout (stock : Stock) (pieces : List Piece) : Layout :=
  ⟨stock.name, stock.extent, pieces, none⟩

private def gridFits (row : StockRow) (contents : List ((Nat × DemandRow) × ExactGrid.Placement)) : Bool :=
  let pieces := contents.map (·.2.piece)
  let payload := (contents.map (·.1.2.weight)).sum
  (gridLayout row.stock pieces).check row.stock && Indexed.checkSheet row.sheet row.stock pieces &&
    Indexed.checkPayload row.payload payload (contents.map (·.1.2.weight))

def evaluateGrid (rows : List DemandRow) (available : List StockRow)
    (plan : List (Option ExactGrid.Placement)) : Option OptScore :=
  let placed := gridTagged (copies rows) plan
  let used := (slotGroups available placed (·.2.slot)).filter (fun (_, ps) => !ps.isEmpty)
  if used.all (fun (row, ps) => gridFits row ps) then
    some (scoreFor rows (placed.map (·.1.1)) used.length
      ((used.map fun (row, _) => row.cost).sum)
      ((used.map fun (row, ps) => volume row.stock.extent - (ps.map (volume ∘ (·.2.piece.extent))).sum).sum))
  else none

private theorem gridTagged_sublist (items : List (Nat × DemandRow)) (plan : List (Option ExactGrid.Placement)) :
    List.Sublist ((gridTagged items plan).map Prod.fst) items := by
  induction items generalizing plan with
  | nil => simp [gridTagged]
  | cons item rest ih =>
    cases plan with
    | nil => simp [gridTagged]
    | cons choice remaining =>
      cases choice with
      | none => exact .cons item (ih remaining)
      | some _ => exact .cons_cons item (ih remaining)

theorem evaluateGrid_profit {rows : List DemandRow} {available : List StockRow}
    {plan : List (Option ExactGrid.Placement)} {score : OptScore}
    (h : evaluateGrid rows available plan = some score) : score.profit ≤ maxProfit rows := by
  simp only [evaluateGrid] at h
  split at h
  next =>
    cases Option.some.inj h
    have hp := (gridTagged_sublist (copies rows) plan).map Prod.fst
    simp only [List.map_map, Function.comp_def] at hp
    exact selectedProfit_le rows _ hp
  next => contradiction

private def anyGrid (rows : List DemandRow) (available : List StockRow)
    (accept : OptScore → Bool) : Bool :=
  anyChoices (gridChoices rows available) fun plan => (evaluateGrid rows available plan).any accept

private def gridBudget (rows : List DemandRow) (available : List StockRow) : Bool :=
  let total := (available.map (volume ∘ Stock.bounds ∘ StockRow.stock)).sum
  total ≤ 65_536 && searchBudget ((copies rows).map fun (_, row) =>
    1 + total * row.demand.orientations.length)

theorem anyGrid_detects (rows : List DemandRow) (available : List StockRow) (accept : OptScore → Bool)
    {plan : List (Option ExactGrid.Placement)} {score : OptScore}
    (hp : GridPlan available (copies rows) plan) (hs : evaluateGrid rows available plan = some score)
    (ha : accept score = true) : anyGrid rows available accept = true :=
  (anyChoices_iff _ _).mpr ⟨plan, gridPlan_covered hp, by simpa [hs] using ha⟩

private theorem gridChoice_admitted {available : List Stock} {demand : Demand}
    {placement : ExactGrid.Placement} (h : placement ∈ ExactGrid.choices available demand) :
    ExactGrid.Admitted available demand placement := by
  unfold ExactGrid.choices at h
  obtain ⟨index, _, h⟩ := List.mem_flatMap.mp h
  cases hs : available[index]? with
  | none => simp [hs] at h
  | some stock =>
    simp only [hs] at h
    obtain ⟨⟨rotation, extent⟩, hr, h⟩ := List.mem_flatMap.mp h
    obtain ⟨cell, _, hc⟩ := List.mem_filterMap.mp h
    split at hc
    next fit =>
      cases Option.some.inj hc
      exact ⟨stock, hs, ⟨rfl, hr⟩, fit⟩
    next => contradiction

private theorem gridChoices_sound {available : List StockRow} {items : List (Nat × DemandRow)}
    {plan : List (Option ExactGrid.Placement)}
    (h : Chooses (Option ExactGrid.Placement)
      (items.map fun (_, row) => none :: (ExactGrid.choices (available.map StockRow.stock) row.demand).map some)
      plan) : GridPlan available items plan := by
  induction items generalizing plan with
  | nil => cases h; exact .nil
  | cons item rest ih =>
    cases h with
    | cons hm ht =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact .skip (ih ht)
      · obtain ⟨placement, hp, rfl⟩ := List.mem_map.mp hm
        exact .place (gridChoice_admitted hp) (ih ht)

theorem anyGrid_iff (rows : List DemandRow) (available : List StockRow) (accept : OptScore → Bool) :
    anyGrid rows available accept = true ↔ ∃ plan score,
      GridPlan available (copies rows) plan ∧ evaluateGrid rows available plan = some score ∧
        accept score = true := by
  constructor
  · intro h
    obtain ⟨plan, hp, ha⟩ := (anyChoices_iff _ _).mp h
    cases hs : evaluateGrid rows available plan with
    | none => simp [hs] at ha
    | some score => exact ⟨plan, score, gridChoices_sound hp, hs, by simpa [hs] using ha⟩
  · rintro ⟨_, _, hp, hs, ha⟩
    exact anyGrid_detects _ _ _ hp hs ha

def checkExactKnapsackGrid (rows : List DemandRow) (stock : List StockRow) (candidate : OptScore) : Bool :=
  let available := slots rows stock
  gridBudget rows available && candidate.missingMinima == 0 &&
    anyGrid rows available (· == candidate) &&
    !anyGrid rows available (cheaperRank rows .knapsack candidate)

theorem exactKnapsackGrid_sound (rows : List DemandRow) (stock : List StockRow) (candidate : OptScore)
    (h : checkExactKnapsackGrid rows stock candidate = true) :
    candidate.missingMinima = 0 ∧
    (∃ plan, GridPlan (slots rows stock) (copies rows) plan ∧
      evaluateGrid rows (slots rows stock) plan = some candidate) ∧
    ∀ plan score, GridPlan (slots rows stock) (copies rows) plan →
      evaluateGrid rows (slots rows stock) plan = some score →
      (¬ Better .knapsack (maxProfit rows) score candidate) ∧
      (score.missingMinima = 0 → score.profit ≤ candidate.profit) := by
  simp only [checkExactKnapsackGrid, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    ← Bool.not_eq_true, anyGrid_iff] at h
  obtain ⟨⟨⟨_, hmin⟩, plan, score, hp, hs, heq⟩, hbetter⟩ := h
  subst score
  refine ⟨hmin, ⟨plan, hp, hs⟩, fun q s hq he => ?_⟩
  have excludes : ¬ Better .knapsack (maxProfit rows) s candidate := fun hb =>
    hbetter ⟨q, s, hq, he, by simpa [cheaperRank, Better] using hb⟩
  refine ⟨excludes, fun hzero => Nat.le_of_not_gt (fun higher => excludes ?_)⟩
  exact better_of_higher_profit (hzero.trans hmin.symm) (evaluateGrid_profit he)
    (evaluateGrid_profit hs) higher

def checkExactCostGrid (rows : List DemandRow) (stock : List StockRow) (candidate : OptScore) : Bool :=
  let available := slots rows stock
  gridBudget rows available && candidate.missingRequested == 0 &&
    anyGrid rows available (· == candidate) &&
    !anyGrid rows available (fun score => score.missingRequested == 0 && score.cost < candidate.cost)

theorem exactCostGrid_sound (rows : List DemandRow) (stock : List StockRow) (candidate : OptScore)
    (h : checkExactCostGrid rows stock candidate = true) :
    candidate.missingRequested = 0 ∧
    (∃ plan, GridPlan (slots rows stock) (copies rows) plan ∧
      evaluateGrid rows (slots rows stock) plan = some candidate) ∧
    ∀ plan score, GridPlan (slots rows stock) (copies rows) plan →
      evaluateGrid rows (slots rows stock) plan = some score →
      score.missingRequested = 0 → candidate.cost ≤ score.cost := by
  simp only [checkExactCostGrid, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    ← Bool.not_eq_true, anyGrid_iff] at h
  obtain ⟨⟨⟨_, hcomplete⟩, plan, _, hp, hs, rfl⟩, hcheaper⟩ := h
  refine ⟨hcomplete, ⟨plan, hp, hs⟩, fun q s hq he hc => Nat.le_of_not_gt (fun hb => ?_)⟩
  exact hcheaper ⟨q, s, hq, he, by simp [hc, hb]⟩

/-- A conservative integer rounding of `load / capacity`. -/
def ceilDiv (load capacity : Nat) : Nat := (load + capacity - 1) / capacity

theorem ceilDiv_le {load capacity count : Nat} (positive : 0 < capacity)
    (fit : load ≤ count * capacity) : ceilDiv load capacity ≤ count := by
  apply (Nat.div_le_iff_le_mul positive).mpr
  omega

theorem count_bound_sound {load capacity : Nat} (loads : List Nat)
    (positive : 0 < capacity) (covers : load ≤ loads.sum)
    (fits : ∀ used ∈ loads, used ≤ capacity) : ceilDiv load capacity ≤ loads.length := by
  apply ceilDiv_le positive
  simpa [Nat.mul_comm] using Nat.le_trans covers (Optimality.total_load_le _ _ fits)

theorem minimum_cost_bound_sound (stockPrices : List Nat) (first : Nat) (rest : List Nat)
    (inStock : first ∈ stockPrices) : stockPrices.min?.getD 0 ≤ (first :: rest).sum := by
  have low := List.min?_getD_le_of_mem (k := 0) inStock
  simpa using Nat.le_trans low (Nat.le_add_right first rest.sum)

theorem open_bound_sound {objective : PackingObjective} {size : Axes} {load : Nat}
    (positive : 0 < fixedExtent objective size) (fit : load ≤ volume size) :
    ceilDiv load (fixedExtent objective size) ≤ extentValue objective size := by
  apply ceilDiv_le positive
  cases objective <;> simpa [volume, extentValue, fixedExtent, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using fit

theorem linear_open_bound_sound {trim kerf extent : Nat} {lengths : List Nat}
    (usable : trim ≤ extent) (fit : linearLength kerf lengths ≤ extent - trim) :
    linearLength kerf lengths + trim ≤ extent := by omega

theorem nested_height_bound (items : List Loading.NestedItem) (base top : Nat)
    (fit : Loading.Nested top base items) :
    base + (items.map (fun item => item.height - item.recess)).sum = top := by
  induction items generalizing base with
  | nil => simpa [Loading.Nested] using fit
  | cons item rest ih =>
    obtain ⟨hl, hb, hr⟩ := fit
    have ht := ih _ hr
    simp only [List.map_cons, List.sum_cons]
    omega

inductive Model where
  | linear | sheet | box | staged | loading
  deriving DecidableEq

private def Model.dimension : Model → Dimension
  | .linear => .linear
  | .sheet | .staged => .sheet
  | .box | .loading => .box

private def Model.stockKey : Model → String
  | .linear => "stock"
  | .sheet | .staged => "sheets"
  | .box | .loading => "bins"

private def Model.extentKeys : Model → List String
  | .linear => ["length"]
  | .sheet | .staged => ["width", "height"]
  | .box | .loading => ["width", "height", "depth"]

private def Model.limitKey : Model → String
  | .linear => "available"
  | _ => "quantity"

private def Model.wrapped (model : Model) : Bool := model == .staged || model == .loading

private def addDefaults (value : Json) (fields : List (String × Json)) : Except String Json := do
  let _ ← value.getObj?
  return (Json.mkObj fields).mergeObj value

private def emptyArray : Json := .arr #[]

private def normalizeStock (model : Model) (stock : Json) : Except String Json :=
  addDefaults stock ([ ("cost", toJson (1 : Nat)), (model.limitKey, .null) ] ++
    match model with
    | .linear => [("kerf", toJson (0 : Nat)), ("trim", toJson (0 : Nat))]
    | .sheet | .staged => [("kerf", toJson (0 : Nat)), ("edge_kerf_relief", toJson false)]
    | _ => [])

private def normalizeDemand (model : Model) (demand : Json) : Except String Json :=
  addDefaults demand (match model with
    | .sheet | .staged => [("can_rotate", toJson true)]
    | .box | .loading => [("allowed_rotations", toJson (63 : Nat))]
    | .linear => [])

private def zeroFields (keys : List String) : List (String × Json) :=
  keys.map fun key => (key, toJson (0 : Nat))

private def nullFields (keys : List String) : List (String × Json) := keys.map (·, .null)

private def normalizeSheet (rules : Json) : Except String Json :=
  addDefaults rules (("defects", emptyArray) :: zeroFields
    ["trim_left", "trim_right", "trim_top", "trim_bottom"])

private def normalizeBin (rules : Json) : Except String Json := do
  let rules ← addDefaults rules (("defects", emptyArray) ::
    nullFields ["maximum_stack_density", "axle_limits"])
  let axles ← rules.getObjVal? "axle_limits"
  if axles == .null then return rules
  return rules.setObjVal! "axle_limits" (← addDefaults axles (zeroFields ["front_tare", "rear_tare"]))

private def normalizeItem (rules : Json) : Except String Json :=
  addDefaults rules (zeroFields ["stackability_id", "nesting_height", "group_id"] ++
    nullFields ["maximum_stackability", "maximum_weight_above"])

private def normalizeStaged (rules : Json) : Except String Json :=
  addDefaults rules ([("max_stages", toJson (3 : Nat)), ("first_axis", toJson "vertical"),
    ("cut_type", toJson "non_exact"), ("cut_through_defects", toJson false)] ++
    zeroFields ["minimum_distance_1_cuts", "minimum_distance_2_cuts", "minimum_waste_length"] ++
    nullFields ["maximum_distance_1_cuts", "maximum_distance_2_cuts", "maximum_number_1_cuts",
      "maximum_number_2_cuts"])

private def mapField (value : Json) (key : String) (f : Json → Except String Json) : Except String Json := do
  let rows ← (← value.getObjValAs? (List Json) key).mapM f
  return value.setObjValAs! key rows

private def normalizeBase (model : Model) (base : Json) : Except String Json := do
  mapField (← mapField base model.stockKey (normalizeStock model)) "demands" (normalizeDemand model)

private def normalizePacking (model : Model) (packing : Json) : Except String Json := do
  if model == .linear then return ← normalizeBase model packing
  let packing := packing.setObjVal! "problem" (← normalizeBase model (← packing.getObjVal? "problem"))
  match model.dimension with
  | .sheet => mapField (← addDefaults packing [("constraints", emptyArray)]) "constraints" normalizeSheet
  | .box => addDefaults packing [("item_weights", emptyArray), ("bin_max_weights", emptyArray)]
  | .linear => throw "unexpected linear packing wrapper"

private def normalizeProblem (model : Model) (problem : Json) : Except String Json := do
  if !model.wrapped then return ← normalizePacking model problem
  let packing ← normalizePacking model (← problem.getObjVal? "packing")
  let problem := problem.setObjVal! "packing" packing
  if model == .staged then
    let problem ← addDefaults problem [("groups", emptyArray), ("rules", Json.mkObj [])]
    return problem.setObjVal! "rules" (← normalizeStaged (← problem.getObjVal? "rules"))
  let problem ← addDefaults problem [("bin_rules", emptyArray), ("item_rules", emptyArray),
    ("unloading", toJson "none")]
  mapField (← mapField problem "bin_rules" normalizeBin) "item_rules" normalizeItem

private def Model.packing (model : Model) (problem : Json) : Except String Json :=
  if model.wrapped then problem.getObjVal? "packing" else pure problem

private def Model.base (model : Model) (packing : Json) : Except String Json :=
  if model == .linear then pure packing else packing.getObjVal? "problem"

private def clipDefects (rules : Json) (axis size axis' size' : String) (cap cap' : Nat) :
    Except String Json := do
  let defects ← (← rules.getObjValAs? (List Json) "defects").filterMapM fun defect => do
    let width := min (← defect.getObjValAs? Nat size) (cap - (← defect.getObjValAs? Nat axis))
    let height := min (← defect.getObjValAs? Nat size') (cap' - (← defect.getObjValAs? Nat axis'))
    return if width == 0 || height == 0 then none else
      some ((defect.setObjValAs! size width).setObjValAs! size' height)
  return rules.setObjValAs! "defects" defects

/-- Reconstruct the one-stock crop, preserving non-open axes and all fixed rules. -/
private def effectiveProblem (model : Model) (objective : PackingObjective) (problem : Json)
    (extents : List Nat) : Except String Json := do
  if objective.axes.isEmpty then
    unless extents.isEmpty do throw "unexpected open extents"
    return problem
  let packing ← model.packing problem
  let base ← model.base packing
  let [stock] ← base.getObjValAs? (List Json) model.stockKey | throw "open crop needs a single stock"
  let keys := model.extentKeys
  unless extents.length == keys.length && objective.axes.all (· < keys.length) do
    throw "unsupported open axes or extent count"
  let mut cropped := stock
  for ((key, extent), axis) in (keys.zip extents).zipIdx do
    let cap ← stock.getObjValAs? Nat key
    unless 0 < extent && extent ≤ cap && cap < 2^32 &&
        (objective.axes.contains axis || extent == cap) do throw "invalid open extent"
    cropped := cropped.setObjValAs! key extent
  let limit ← stock.getObjValAs? (Option Nat) model.limitKey
  cropped := cropped.setObjValAs! model.limitKey (min 1 (limit.getD 1))
  let base := base.setObjValAs! model.stockKey [cropped]
  let size ← readExtent model.dimension cropped
  if model == .linear then
    unless (← cropped.getObjValAs? Nat "trim") < size.x do throw "crop leaves no usable stock"
    return base
  let mut packing := packing.setObjVal! "problem" base
  if model.dimension matches .sheet then
    let rules ← packing.getObjValAs? (List Json) "constraints"
    match rules with
    | [] => pure ()
    | [rule] =>
      let trim ← fromJson? (α := Indexed.Trim) rule
      unless trim.trim_left + trim.trim_right < size.x && trim.trim_top + trim.trim_bottom < size.y do
        throw "crop leaves no usable sheet"
      packing := packing.setObjValAs! "constraints" [← clipDefects rule "x" "width" "y" "height" size.x size.y]
    | _ => throw "incorrect sheet rule count"
  if model == .staged then return problem.setObjVal! "packing" packing
  if model == .loading then
    let rules ← problem.getObjValAs? (List Json) "bin_rules"
    let rules ← match rules with
      | [] => pure []
      | [rule] => do
        let parsed ← fromJson? (α := Loading.BinRule) rule
        if let some axles := parsed.axle_limits then
          let length := match axles.axis with | .x => size.x | .z => size.z
          unless axles.rear_position ≤ length do throw "crop excludes fixed axle support"
        pure [← clipDefects rule "x" "width" "z" "depth" size.x size.z]
      | _ => throw "incorrect bin rule count"
    return (problem.setObjVal! "packing" packing).setObjValAs! "bin_rules" rules
  return packing

private def totalLoad (model : Model) (demands : List Demand) (nesting : List Loading.ItemRule) : Nat :=
  (demands.zipIdx.map fun (demand, index) =>
    let size := demand.extent
    let recess := if model == .loading then (nesting[index]?.getD {}).nesting_height else 0
    volume {size with y := size.y - recess} * demand.quantity).sum

private def positiveExtent (size : Axes) : Bool :=
  0 < size.x && 0 < size.y && 0 < size.z && size.x < 2^32 && size.y < 2^32 && size.z < 2^32

private structure ReadProblem where
  raw : Json
  demands : List DemandRow
  stocks : List StockRow
  load : Nat

private def readProblem (model : Model) (problem : Json) (profits : List Nat := [])
    (minima : List Nat := []) : Except String ReadProblem := do
  let raw ← normalizeProblem model problem
  let packing ← model.packing raw
  let base ← model.base packing
  let demands ← (← base.getObjValAs? (List Json) "demands").mapM (readDemand model.dimension)
  let rawStocks ← base.getObjValAs? (List Json) model.stockKey
  let stocks ← rawStocks.mapM (readStock model.dimension)
  unless !stocks.isEmpty && !demands.isEmpty && stocks.all (fun s => positiveExtent s.extent &&
      0 < s.bounds.x && s.gap < 2^32) && demands.all (fun d => positiveExtent d.extent &&
      0 < d.quantity && !d.orientations.isEmpty) do throw "invalid stock or demand dimensions"
  let (weights, limits) ←
    if model.dimension matches .box then do
      let weights ← packing.getObjValAs? (List Nat) "item_weights"
      let limits ← packing.getObjValAs? (List (Option Nat)) "bin_max_weights"
      unless (weights.isEmpty || weights.length == demands.length) &&
          (limits.isEmpty || limits.length == stocks.length) && weights.all (· < 2^64) &&
          limits.all (fun limit => limit.all (· < 2^64)) do throw "invalid source payload arrays"
      pure (weights, limits)
    else pure ([], [])
  let sheets ← if model.dimension matches .sheet then do
      let rules ← Indexed.sheetRules packing stocks
      for (stock, rule) in stocks.zip rules do
        let trim := rule.trim
        unless stock.bounds == stock.extent && trim.trim_left + trim.trim_right < stock.extent.x &&
            trim.trim_top + trim.trim_bottom < stock.extent.y && rule.defects.all (fun defect =>
              positiveExtent defect.extent && defect.origin.x + defect.extent.x ≤ stock.extent.x &&
                defect.origin.y + defect.extent.y ≤ stock.extent.y) do throw "invalid physical sheet rules"
      pure rules
    else pure (List.replicate stocks.length {})
  let prices ← rawStocks.mapM fun stock => do readAmount (← stock.getObjVal? "cost")
  let rows := demands.zipIdx.map fun (demand, index) =>
    DemandRow.mk demand (profits[index]?.getD dyadicScale) (minima[index]?.getD 0) (weights[index]?.getD 0)
  unless (profits.isEmpty || profits.length == demands.length) &&
      (minima.isEmpty || minima.length == demands.length) &&
      rows.all (fun row => row.minimum ≤ row.demand.quantity) do throw "invalid source value arrays"
  let nesting ← if model == .loading then raw.getObjValAs? (List Loading.ItemRule) "item_rules" else pure []
  return ⟨raw, rows, (stocks.zip prices).zipIdx.map (fun ((stock, cost), index) =>
    ⟨stock, cost, sheets[index]?.getD {}, limits[index]?.join⟩), totalLoad model demands nesting⟩

private def readLinear (base solution : Json) (stockIndices : List Nat) (demandIndices : List (List Nat)) :
    Except String Indexed.Readback := do
  let stocks ← (← base.getObjValAs? (List Json) "stock").mapM (readStock .linear)
  let demands ← (← base.getObjValAs? (List Json) "demands").mapM (readDemand .linear)
  let raws ← solution.getObjValAs? (List Json) "layouts"
  unless raws.length == stockIndices.length && raws.length == demandIndices.length do
    throw "incorrect linear layout provenance length"
  let layouts ← (raws.zip (stockIndices.zip demandIndices)).mapM fun (raw, stockIndex, indices) => do
    let some stock := stocks[stockIndex]? | throw "unknown linear stock source"
    let layout ← readLayout .linear [stock] raw
    unless !layout.pieces.isEmpty && layout.pieces.length == indices.length do
      throw "incorrect linear cut provenance length"
    let pieces ← (layout.pieces.zip indices).mapM fun (piece, index) => do
      let some demand := demands[index]? | throw "unknown linear demand source"
      unless piece.name == demand.name do throw "cut name differs from source"
      return { piece with name := Indexed.sourceKey index }
    return Indexed.IndexedLayout.mk stockIndex indices
      {layout with stock := Indexed.sourceKey stockIndex, pieces := pieces}
  let result := Indexed.Readback.mk stocks demands layouts (← solution.getObjValAs? Nat "stock_count")
  let reported ← (← solution.getObjValAs? (List Json) "unplaced").mapM fun cut => do
    let shortage ← readShortage .linear cut
    return Demand.mk shortage.name shortage.extent 1 [("identity", shortage.extent)]
  unless Indexed.checkShortages result.shortages reported do throw "incorrect reported linear shortage"
  return result

private def materialTotals (model : Model) (solution : Json) (result : Indexed.Readback)
    (stocks : List StockRow) : Except String (Nat × Nat) := do
  let raws ← solution.getObjValAs? (List Json) "layouts"
  let mut cost := 0
  let mut waste := 0
  for (row, raw) in result.layouts.zip raws do
    let some source := stocks[row.stockIndex]? | throw "unknown layout stock source"
    unless (← readAmount (← raw.getObjVal? "cost")) == source.cost do throw "incorrect layout cost"
    cost := cost + source.cost
    unless cost ≤ maxExactUnits do throw exactAmountError
    if model == .linear then
      let some summary := row.layout.linear | throw "missing linear length summary"
      waste := waste + summary.waste
    else
      let used := Optimality.usedVolume row.layout
      let unused := volume source.stock.extent - used
      let suffix := if model == .box then "volume" else "area"
      unless used == (← raw.getObjValAs? Nat ("used_" ++ suffix)) &&
          unused == (← raw.getObjValAs? Nat ("waste_" ++ suffix)) do throw "incorrect layout usage"
      waste := waste + unused
  let wasteKey := match model with
    | .linear => "total_waste"
    | .box => "total_waste_volume"
    | _ => "total_waste_area"
  unless cost == (← readAmount (← solution.getObjVal? "total_cost")) &&
      waste == (← solution.getObjValAs? Nat wasteKey) do throw "incorrect total stock usage"
  return (cost, waste)

private def checkLoadingReadback (problem : ReadProblem) (solution : Json) (stockIndices : List Nat)
    (demandIndices : List (List Nat)) : Except String (Nat × Nat) := do
  let layouts ← solution.getObjValAs? (List Loading.BinLayout) "layouts"
  unless stockIndices == layouts.map Loading.BinLayout.bin_index &&
      demandIndices == layouts.map (fun layout => layout.stacks.flatMap fun column =>
        column.items.map Loading.ItemPlacement.demand_index) &&
      (← Loading.checkLoading problem.raw solution) do throw "invalid loading certificate"
  let mut cost := 0
  let mut waste := 0
  for layout in layouts do
    let some stock := problem.stocks[layout.bin_index]? | throw "unknown loaded stock"
    let used := (layout.stacks.map fun stack => volume ⟨stack.width, stack.height, stack.depth⟩).sum
    cost := cost + stock.cost
    unless cost ≤ maxExactUnits do throw exactAmountError
    waste := waste + (volume stock.stock.extent - used)
  unless cost == (← readAmount (← solution.getObjVal? "total_cost")) do throw "incorrect loading cost"
  return (cost, waste)

private def checkReadback (model : Model) (problem : ReadProblem) (solution : Json) (stockIndices : List Nat)
    (demandIndices : List (List Nat)) : Except String (Nat × Nat) := do
  let packing ← model.packing problem.raw
  let base ← model.base packing
  match model with
  | .loading => checkLoadingReadback problem solution stockIndices demandIndices
  | .linear =>
    let result ← readLinear base solution stockIndices demandIndices
    unless result.certificate.check do throw "invalid linear certificate"
    materialTotals model solution result problem.stocks
  | .sheet | .box | .staged =>
    let wrapped ← match model with
      | .staged =>
        unless stockIndices == (← solution.getObjValAs? (List Nat) "stock_indices") &&
            demandIndices == (← solution.getObjValAs? (List (List Nat)) "demand_indices") &&
            (← Staged.checkStaged problem.raw solution) do throw "invalid staged certificate"
        pure solution
      | .sheet =>
        let wrapped := Json.mkObj [("solution", solution), ("stock_indices", toJson stockIndices),
          ("demand_indices", toJson demandIndices)]
        unless !(← solution.getObjValAs? Bool "guillotine") &&
            (← Indexed.checkConstrained .sheet packing wrapped) do throw "invalid sheet certificate"
        pure wrapped
      | _ =>
        let weights := demandIndices.map fun layout =>
          (layout.map fun index => (problem.demands[index]?.map DemandRow.weight).getD 0).sum
        let wrapped := Json.mkObj [("solution", solution), ("bin_indices", toJson stockIndices),
          ("demand_indices", toJson demandIndices), ("bin_weights", toJson weights)]
        unless ← Indexed.checkConstrained .box packing wrapped do throw "invalid box certificate"
        pure wrapped
    let result ← Indexed.readIndexed model.dimension base wrapped
    materialTotals model (← wrapped.getObjVal? "solution") result problem.stocks

private def reportValue (objective : PackingObjective) (score : OptScore) : Nat :=
  match objective with
  | .knapsack => score.profit
  | .total_cost => score.cost
  | .bin_count => score.containers * dyadicScale
  | .feasibility => score.missingRequested * dyadicScale
  | _ => extentValue objective score.extent * dyadicScale

private def reportBound (model : Model) (objective : PackingObjective) (problem : ReadProblem)
    (first : Stock) : Nat :=
  match objective with
  | .knapsack => maxProfit problem.demands
  | .total_cost => ((problem.stocks.map StockRow.cost).min?).getD 0
  | .feasibility => 0
  | .bin_count =>
    let capacity := (problem.stocks.map (fun row => if model == .linear then row.stock.bounds.x
        else volume row.stock.extent)).max?.getD 1
    ceilDiv problem.load capacity * dyadicScale
  | _ =>
    if model == .linear then
      let count := (problem.demands.map (·.demand.quantity)).sum
      (problem.load + (first.extent.x - first.bounds.x) + first.gap * (count - 1)) * dyadicScale
    else ceilDiv problem.load (fixedExtent objective first.extent) * dyadicScale

private def checkOptimized (model : Model) (input output : Json) : Except String Bool := do
  let source ← input.getObjVal? "problem"
  let options ← input.getObjVal? "options"
  let objective ← readDefault options "objective" PackingObjective.bin_count
  let maxEvaluations ← readDefault options "max_evaluations" (128 : Nat)
  let beam ← readDefault options "beam_width" (8 : Nat)
  let maxStates ← readDefault options "packing_max_states" (256 : Nat)
  let seed ← readDefault options "seed" (0 : Nat)
  unless seed < 2^64 && 0 < maxEvaluations && maxEvaluations ≤ 4096 && 0 < beam && beam ≤ 32 &&
      maxStates ≤ 100_000 do return false
  let profits ← (← readDefault source "profits" ([] : List Json)).mapM readAmount
  let minima ← readDefault source "minimum_quantities" ([] : List Nat)
  let problem ← readProblem model (← source.getObjVal? "packing") profits minima
  let some first := problem.stocks.head? | return false
  let requested := problem.demands.map (·.demand.quantity)
  unless requested.length ≤ 16 && requested.sum ≤ 128 && problem.stocks.length ≤ 16 do return false
  -- Every nonnegative partial profit sum is bounded by the profit of all requested copies.
  unless maxProfit problem.demands ≤ maxExactUnits do throw exactAmountError
  let report ← output.getObjVal? "report"
  let evaluations ← report.getObjValAs? Nat "evaluations"
  let packingStates ← report.getObjValAs? Nat "packing_states"
  let _ ← report.getObjValAs? Bool "search_truncated"
  unless packingStates < 2^64 && (← report.getObjValAs? PackingObjective "objective") == objective &&
      0 < evaluations && evaluations ≤ maxEvaluations do return false
  let extents ← report.getObjValAs? (List Nat) "open_extents"
  let expected ← effectiveProblem model objective problem.raw extents
  let effective ← readProblem model (← output.getObjVal? "effective_problem") profits minima
  unless effective.raw == expected do return false
  let stockIndices ← output.getObjValAs? (List Nat) "stock_indices"
  let demandIndices ← output.getObjValAs? (List (List Nat)) "demand_indices"
  let (cost, waste) ← checkReadback model effective (← output.getObjVal? "solution") stockIndices demandIndices
  let placed := demandIndices.flatten
  let selected := problem.demands.zipIdx.map fun (_, index) => placed.count index
  let some effectiveStock := effective.stocks.head? | return false
  let score := scoreFor problem.demands placed stockIndices.length cost waste effectiveStock.stock.extent
  unless score.profit ≤ maxExactUnits do throw exactAmountError
  let complete := score.missingRequested == 0
  let minimumsSatisfied := score.missingMinima == 0
  let value := reportValue objective score
  let bound := reportBound model objective problem first.stock
  let optimal ← report.getObjValAs? Bool "primary_optimal"
  let reportedBound ← readAmount (← report.getObjVal? "primary_bound")
  return selected == (← report.getObjValAs? (List Nat) "selected_quantities") &&
    complete == (← report.getObjValAs? Bool "complete") &&
    minimumsSatisfied == (← report.getObjValAs? Bool "minimums_satisfied") &&
    score.profit == (← readAmount (← report.getObjVal? "total_profit")) &&
    value == (← readAmount (← report.getObjVal? "primary_value")) && reportedBound == bound &&
    (objective == .knapsack) == (← report.getObjValAs? Bool "bound_is_upper") &&
    (!optimal || (if objective == .knapsack then minimumsSatisfied else complete) && value == bound)

/-- Verify a source-indexed optimized linear output, including its objective report. -/
def checkOptimized1D (input output : Json) : Except String Bool := checkOptimized .linear input output

/-- Verify a source-indexed optimized rectangular output with trim and defects. -/
def checkOptimized2D (input output : Json) : Except String Bool := checkOptimized .sheet input output

/-- Verify a source-indexed optimized cuboid output with payload constraints. -/
def checkOptimized3D (input output : Json) : Except String Bool := checkOptimized .box input output

/-- Verify a source-indexed optimized staged cutting output. -/
def checkOptimizedStaged2D (input output : Json) : Except String Bool := checkOptimized .staged input output

/-- Verify a source-indexed optimized loading output. -/
def checkOptimizedLoading3D (input output : Json) : Except String Bool := checkOptimized .loading input output

private theorem sumPartition (entries : List α) (select : α → Bool) (weight : α → Nat) :
    ((entries.filter select).map weight).sum + ((entries.filter (fun entry => !select entry)).map weight).sum =
      (entries.map weight).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases test : select entry <;>
      simp only [List.filter_cons, test, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.map_cons, List.sum_cons] <;> omega

private theorem groupWeight (available : List StockRow) (entries : List α) (key weight : α → Nat)
    (start : Nat) (within : ∀ entry ∈ entries, start ≤ key entry ∧ key entry < start + available.length) :
    ((slotGroups available entries key start).map (fun (_, es) => (es.map weight).sum)).sum =
      (entries.map weight).sum := by
  induction available generalizing entries start with
  | nil =>
    cases entries with
    | nil => rfl
    | cons entry rest => have := within entry (by simp); simp at this; omega
  | cons row rest ih =>
    let remaining := entries.filter (fun entry => !(key entry == start))
    have outside : ∀ entry ∈ remaining, start + 1 ≤ key entry ∧ key entry < start + 1 + rest.length := by
      intro entry h
      have ⟨hm, hne⟩ := List.mem_filter.mp h
      have hb := within entry hm
      simp at hne
      simp only [List.length_cons] at hb
      omega
    have same : slotGroups rest entries key (start + 1) = slotGroups rest remaining key (start + 1) := by
      unfold slotGroups
      apply List.map_congr_left
      intro slot hm
      have hlo := List.le_snd_of_mem_zipIdx hm
      apply congrArg (slot.1, ·)
      simp only [remaining, List.filter_filter]
      apply List.filter_congr
      intro entry _
      by_cases hs : key entry = slot.2
      · have hne : slot.2 ≠ start := by omega
        simp [hs, hne]
      · simp [hs]
    change ((entries.filter (fun entry => key entry == start)).map weight).sum +
      ((slotGroups rest entries key (start + 1)).map (fun (_, es) => (es.map weight).sum)).sum = _
    rw [same, ih remaining (start + 1) outside]
    exact sumPartition entries _ weight

private theorem groupCapacity (available : List StockRow) (entries : List α) (key weight : α → Nat)
    (capacity : StockRow → Nat) (start : Nat)
    (fits : ∀ slot ∈ slotGroups available entries key start,
      (slot.2.map weight).sum ≤ capacity slot.1) :
    ((slotGroups available entries key start).map (fun (_, es) => (es.map weight).sum)).sum ≤
      (available.map capacity).sum := by
  induction available generalizing start with
  | nil => simp [slotGroups]
  | cons row rest ih =>
    change ∀ slot ∈ (row, entries.filter (fun entry => key entry == start)) ::
      slotGroups rest entries key (start + 1), _ at fits
    exact Nat.add_le_add (fits (row, entries.filter (fun entry => key entry == start)) (by simp)) (ih (start + 1) (fun slot hm => fits slot (by simp [hm])))

private theorem linearPlan_bounds {items : List α} {count : Nat} {plan : List Nat}
    (hp : Chooses Nat (items.map (fun _ => List.range count)) plan) :
    plan.length = items.length ∧ ∀ slot ∈ plan, slot < count := by
  induction items generalizing plan with
  | nil => cases hp; simp
  | cons item rest ih =>
    cases hp with
    | cons hm ht =>
      obtain ⟨hsize, hslots⟩ := ih ht
      exact ⟨by simp [hsize], by simpa using And.intro (List.mem_range.mp hm) hslots⟩

private theorem linearGroups_fit {rows : List DemandRow} {available : List StockRow} {plan : List Nat}
    (h : (evaluateLinear rows available plan).isSome = true) :
    ∀ slot ∈ slotGroups available (linearTagged rows plan) Prod.snd 1,
      linearFits slot.1 slot.2 = true := by
  simp only [evaluateLinear] at h
  split at h
  next hall =>
    intro slot hm
    by_cases he : slot.2 = []
    · simp [linearFits, linearLengths, linearLength, he]
    · exact List.all_eq_true.mp hall slot (List.mem_filter.mpr ⟨hm, by simpa using he⟩)
  next => simp at h

private def linearPadded (kerf : Nat) (row : DemandRow) : Nat := row.demand.extent.x + kerf

private theorem linearInventory {rows : List DemandRow} {available : List StockRow} {plan : List Nat}
    (hp : LinearPlan rows available plan) (complete : 0 ∉ plan)
    (fit : (evaluateLinear rows available plan).isSome = true) (kerf : Nat)
    (hkerf : ∀ row ∈ available, kerf ≤ row.stock.gap) :
    ((copies rows).map (linearPadded kerf ∘ Prod.snd)).sum ≤
      (available.map (fun row => row.stock.bounds.x + kerf)).sum := by
  obtain ⟨hlen, hslots⟩ := linearPlan_bounds hp
  let entries := linearTagged rows plan
  have hwithin : ∀ entry ∈ entries, 1 ≤ entry.2 ∧ entry.2 < 1 + available.length := by
    intro entry hm
    have hs := List.of_mem_zip hm |>.2
    have hpos : entry.2 ≠ 0 := fun hz => complete (hz ▸ hs)
    have hlt := hslots _ hs
    omega
  let weight := fun entry : (Nat × DemandRow) × Nat => linearPadded kerf entry.1.2
  have hsum := groupWeight available entries Prod.snd weight 1 hwithin
  have hcap := groupCapacity available entries Prod.snd weight
    (fun row => row.stock.bounds.x + kerf) 1 (by
      intro slot hm
      have hfit := linearGroups_fit fit slot hm
      have hmem : slot.1 ∈ available := by
        obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hm
        exact List.fst_mem_of_mem_zipIdx hs
      have hmono := Nat.mul_le_mul_right ((linearLengths slot.2).length - 1) (hkerf _ hmem)
      have hload : linearLength kerf (linearLengths slot.2) ≤ slot.1.stock.bounds.x := by
        simp only [linearFits, decide_eq_true_eq] at hfit
        unfold linearLength at *
        omega
      simpa [weight, Optimality.paddedLoad, linearLengths, linearPadded, List.map_map, Function.comp_def] using
        Optimality.paddedLoad_fits kerf slot.1.stock.bounds.x (linearLengths slot.2) hload)
  rw [hsum] at hcap
  change (((copies rows).zip plan).map ((linearPadded kerf ∘ Prod.snd) ∘ Prod.fst)).sum ≤ _ at hcap
  rw [← List.map_map (f := Prod.fst), List.map_fst_zip (by omega :
    (copies rows).length ≤ plan.length)] at hcap
  exact hcap

private theorem mem_le_sum {value : Nat} {values : List Nat} (h : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => simp at h
  | cons head tail ih =>
    simp only [List.mem_cons, List.sum_cons] at *
    rcases h with rfl | hm
    · omega
    · have := ih hm; omega

private theorem linearOversize {rows : List DemandRow} {available : List StockRow} {plan : List Nat}
    (hp : LinearPlan rows available plan) (complete : 0 ∉ plan)
    (fit : (evaluateLinear rows available plan).isSome = true) :
    ∀ item ∈ copies rows, ∃ stock ∈ available, item.2.demand.extent.x ≤ stock.stock.bounds.x := by
  obtain ⟨hlen, hslots⟩ := linearPlan_bounds hp
  intro item hm
  rw [← List.map_fst_zip (by omega : (copies rows).length ≤ plan.length)] at hm
  obtain ⟨⟨given, index⟩, hentry, rfl⟩ := List.mem_map.mp hm
  have hs := List.of_mem_zip hentry |>.2
  have hpos : 1 ≤ index := by have : index ≠ 0 := fun h => complete (h ▸ hs); omega
  have hlt := hslots _ hs
  let stock := available[index - 1]'(by omega)
  have hstock : (stock, index) ∈ available.zipIdx 1 :=
    List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨hpos, List.getElem?_eq_getElem _⟩
  let es := (linearTagged rows plan).filter (fun entry => entry.2 == index)
  have hslot : (stock, es) ∈ slotGroups available (linearTagged rows plan) Prod.snd 1 :=
    List.mem_map.mpr ⟨(stock, index), hstock, rfl⟩
  have hload := linearGroups_fit fit (stock, es) hslot
  have hm : given.2.demand.extent.x ∈ linearLengths es :=
    List.mem_map.mpr ⟨(given, index), List.mem_filter.mpr ⟨hentry, by simp⟩, rfl⟩
  have hle := mem_le_sum hm
  have hlength : (linearLengths es).sum + stock.stock.gap * ((linearLengths es).length - 1) ≤
      stock.stock.bounds.x := of_decide_eq_true hload
  refine ⟨stock, List.fst_mem_of_mem_zipIdx hstock, ?_⟩
  change given.2.demand.extent.x ≤ stock.stock.bounds.x
  omega

inductive InfeasibilityWitness where
  | oversize
  | inventory
  | exhaustive
  deriving DecidableEq, FromJson

def CompleteLinear (rows : List DemandRow) (available : List StockRow) (plan : List Nat) : Prop :=
  LinearPlan rows available plan ∧ 0 ∉ plan ∧ (evaluateLinear rows available plan).isSome = true

private def anyCompleteLinear (rows : List DemandRow) (available : List StockRow) : Bool :=
  anyChoices (linearChoices rows available) fun plan => !(plan.contains 0) &&
    (evaluateLinear rows available plan).isSome

private theorem anyCompleteLinear_iff {rows : List DemandRow} {available : List StockRow} :
    anyCompleteLinear rows available = true ↔ ∃ plan, CompleteLinear rows available plan := by
  simp [anyCompleteLinear, anyChoices_iff, CompleteLinear, LinearPlan, Bool.and_eq_true,
    ← Bool.not_eq_true]

private def oversizeWitness (rows : List DemandRow) (stock : List StockRow)
    (tooLarge : DemandRow → StockRow → Bool) : Bool :=
  rows.any fun row => 0 < row.demand.quantity &&
    stock.all fun source => source.stock.limit == some 0 || tooLarge row source

private theorem slot_has_stock {rows : List DemandRow} {stock : List StockRow} {source : StockRow}
    (h : source ∈ slots rows stock) : source ∈ stock ∧ source.stock.limit ≠ some 0 := by
  obtain ⟨row, hr, hcopies⟩ := List.mem_flatMap.mp h
  obtain ⟨hcount, rfl⟩ := List.mem_replicate.mp hcopies
  refine ⟨hr, fun hzero => ?_⟩
  simp [stockMultiplicity, hzero] at hcount

private theorem oversizeWitness_item {rows : List DemandRow} {stock : List StockRow}
    {tooLarge : DemandRow → StockRow → Bool} (h : oversizeWitness rows stock tooLarge = true) :
    ∃ item ∈ copies rows, ∀ source ∈ slots rows stock, tooLarge item.2 source = true := by
  simp only [oversizeWitness, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨row, hm, hpos, hsize⟩ := h
  have indexed : row ∈ rows.zipIdx.map Prod.fst := by simpa using hm
  obtain ⟨⟨source, index⟩, hi, heq⟩ := List.mem_map.mp indexed
  change source = row at heq
  subst source
  refine ⟨(index, row), List.mem_flatMap.mpr ⟨(row, index), hi,
    List.mem_replicate.mpr ⟨Nat.ne_of_gt hpos, rfl⟩⟩, ?_⟩
  intro source hs
  obtain ⟨hr, nonzero⟩ := slot_has_stock hs
  simpa [nonzero] using hsize source hr

private def demandTotal (rows : List DemandRow) (weight : DemandRow → Nat) : Nat :=
  (rows.map fun row => row.demand.quantity * weight row).sum

private theorem sum_copies (rows : List DemandRow) (weight : DemandRow → Nat) :
    ((copies rows).map (weight ∘ Prod.snd)).sum = demandTotal rows weight := by
  have indexed (entries : List (DemandRow × Nat)) :
      ((entries.flatMap fun (row, index) => List.replicate row.demand.quantity (index, row)).map
        (weight ∘ Prod.snd)).sum = (entries.map fun (row, _) => row.demand.quantity * weight row).sum := by
    induction entries with
    | nil => rfl
    | cons entry rest ih =>
      simp [List.map_append, List.sum_replicate_nat, ih]
  rw [copies, indexed]
  have sameRows := congrArg (fun entries : List DemandRow => demandTotal entries weight)
    (List.zipIdx_map_fst 0 rows)
  simpa only [demandTotal, List.map_map, Function.comp_def] using sameRows

private def slotTotal (cap : Nat) (stock : List StockRow) (weight : StockRow → Nat) : Nat :=
  (stock.map fun row => stockMultiplicity cap row * weight row).sum

private def inventoryCapacity (stock : List StockRow) (weight : StockRow → Nat) : Nat :=
  (stock.map fun row => row.stock.limit.getD 0 * weight row).sum

private theorem sum_slots (rows : List DemandRow) (stock : List StockRow) (weight : StockRow → Nat) :
    ((slots rows stock).map weight).sum = slotTotal (rows.map (·.demand.quantity)).sum stock weight := by
  induction stock with
  | nil => rfl
  | cons row rest ih =>
    simp only [slots, slotTotal, List.flatMap_cons, List.map_append, List.map_replicate,
      List.sum_append_nat, List.sum_replicate_nat, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

private theorem slots_capacity_le (rows : List DemandRow) (stock : List StockRow)
    (weight : StockRow → Nat) (finite : stock.all (·.stock.limit.isSome) = true) :
    ((slots rows stock).map weight).sum ≤ inventoryCapacity stock weight := by
  rw [sum_slots]
  apply sumWeight_le
  intro row hm
  have hf := List.all_eq_true.mp finite row hm
  cases h : row.stock.limit with
  | none => simp [h] at hf
  | some limit =>
    simpa [stockMultiplicity, h] using
      (Nat.mul_le_mul_right (weight row) (Nat.min_le_right (rows.map (·.demand.quantity)).sum limit))

private def inventoryKerf (stock : List StockRow) : Nat :=
  ((stock.filter (fun row => row.stock.limit != some 0)).map (·.stock.gap)).min?.getD 0

def checkInfeasible1D (rows : List DemandRow) (stock : List StockRow) (witness : InfeasibilityWitness) : Bool :=
  match witness with
  | .oversize => oversizeWitness rows stock fun row source => source.stock.bounds.x < row.demand.extent.x
  | .inventory =>
    let kerf := inventoryKerf stock
    stock.all (·.stock.limit.isSome) &&
      inventoryCapacity stock (fun row => row.stock.bounds.x + kerf) < demandTotal rows (linearPadded kerf)
  | .exhaustive =>
    let count := (rows.map (·.demand.quantity)).sum
    if count > 128 then false else
      let slotCount := slotTotal count stock (fun _ => 1)
      if (slotCount + 1) ^ count > 65_536 then false else
        !anyCompleteLinear rows (slots rows stock)

theorem infeasible1D_sound (rows : List DemandRow) (stock : List StockRow) (witness : InfeasibilityWitness)
    (h : checkInfeasible1D rows stock witness = true) :
    ¬ ∃ plan, CompleteLinear rows (slots rows stock) plan := by
  rintro ⟨plan, hp, hc, hf⟩
  cases witness with
  | oversize =>
    obtain ⟨item, hm, hsize⟩ := oversizeWitness_item h
    obtain ⟨source, hs, hfit⟩ := linearOversize hp hc hf item hm
    exact Nat.not_lt_of_ge hfit (of_decide_eq_true (hsize source hs))
  | inventory =>
    simp only [checkInfeasible1D, Bool.and_eq_true, decide_eq_true_eq] at h
    let kerf := inventoryKerf stock
    have hkerf : ∀ row ∈ slots rows stock, kerf ≤ row.stock.gap := by
      intro row hm
      obtain ⟨hs, nonzero⟩ := slot_has_stock hm
      have hw := List.mem_map_of_mem (f := fun source : StockRow => source.stock.gap)
        ((List.mem_filter (p := fun source => source.stock.limit != some 0)).mpr ⟨hs, by simp [nonzero]⟩)
      exact List.min?_getD_le_of_mem hw
    have load := linearInventory hp hc hf kerf hkerf
    rw [sum_copies] at load
    exact Nat.not_lt_of_ge (Nat.le_trans load (slots_capacity_le rows stock _ h.1)) h.2
  | exhaustive =>
    have complete := anyCompleteLinear_iff.mpr ⟨plan, hp, hc, hf⟩
    simp [checkInfeasible1D, complete] at h

private theorem gridTagged_complete {available : List StockRow} {items : List (Nat × DemandRow)}
    {plan : List (Option ExactGrid.Placement)} (hp : GridPlan available items plan) (hc : none ∉ plan) :
    (gridTagged items plan).map Prod.fst = items ∧
    ∀ entry ∈ gridTagged items plan, ExactGrid.Admitted (available.map StockRow.stock) entry.1.2.demand entry.2 := by
  induction hp with
  | nil => simp [gridTagged]
  | skip => simp at hc
  | place ha _ ih =>
    obtain ⟨heq, hall⟩ := ih (by simpa using hc)
    simp only [gridTagged, List.zip_cons_cons, List.filterMap_cons, Option.map_some, List.map_cons,
      List.cons.injEq, true_and, List.mem_cons] at *
    exact ⟨heq, fun entry h => (h.elim (fun he => he ▸ ha) (hall entry))⟩


theorem nested_column_bound (items : List Loading.NestedItem) (top footprint : Nat)
    (nesting : Loading.Nested top 0 items) (paidHeight : Loading.NestedItem → Nat)
    (conservative : ∀ item ∈ items, paidHeight item ≤ item.height - item.recess) :
    footprint * (items.map paidHeight).sum ≤ footprint * top := by
  have hsum := sumWeight_le items paidHeight (fun item => item.height - item.recess) conservative
  have htop := nested_height_bound items 0 top nesting
  simp only [Nat.zero_add] at htop
  rw [htop] at hsum
  exact Nat.mul_le_mul_left footprint hsum

theorem knapsack_bound_sound (quantities : List (Nat × Nat)) (profits : List Nat)
    (fits : ∀ pair ∈ quantities, pair.1 ≤ pair.2) :
    profitOf (quantities.map Prod.fst) profits ≤ profitOf (quantities.map Prod.snd) profits := by
  simp only [profitOf, List.zip_map_left, List.map_map, Function.comp_def, Prod.map]
  apply sumWeight_le
  intro entry hm
  exact Nat.mul_le_mul_right entry.2 (fits entry.1 (List.of_mem_zip hm).1)

private def gridLoad (row : DemandRow) : Nat :=
  (row.demand.orientations.map (volume ∘ Prod.snd)).min?.getD 0

private theorem gridGroups_fit {rows : List DemandRow} {available : List StockRow}
    {plan : List (Option ExactGrid.Placement)} (h : (evaluateGrid rows available plan).isSome = true) :
    ∀ slot ∈ slotGroups available (gridTagged (copies rows) plan) (·.2.slot),
      (gridLayout slot.1.stock (slot.2.map (·.2.piece))).Valid slot.1.stock := by
  simp only [evaluateGrid] at h
  split at h
  next hall =>
    intro slot hm
    apply (Layout.check_iff _ _).mp
    by_cases he : slot.2 = []
    · simp [gridLayout, Layout.check, he]
    · have hfit := List.all_eq_true.mp hall slot (List.mem_filter.mpr ⟨hm, by simpa using he⟩)
      simp only [gridFits, Bool.and_eq_true] at hfit
      exact hfit.1.1
  next => simp at h

private theorem gridInventory {rows : List DemandRow} {available : List StockRow}
    {plan : List (Option ExactGrid.Placement)} (hp : GridPlan available (copies rows) plan)
    (complete : none ∉ plan) (fit : (evaluateGrid rows available plan).isSome = true) :
    ((copies rows).map (gridLoad ∘ Prod.snd)).sum ≤
      (available.map (volume ∘ Stock.bounds ∘ StockRow.stock)).sum := by
  let entries := gridTagged (copies rows) plan
  obtain ⟨hcopies, hadmit⟩ := gridTagged_complete hp complete
  have hwithin : ∀ entry ∈ entries, 0 ≤ entry.2.slot ∧ entry.2.slot < 0 + available.length := by
    intro entry hm
    obtain ⟨stock, hs, _⟩ := hadmit entry hm
    simpa using (List.getElem?_eq_some_iff.mp hs).1
  let weight := fun entry : (Nat × DemandRow) × ExactGrid.Placement => volume entry.2.piece.extent
  let capacity := volume ∘ Stock.bounds ∘ StockRow.stock
  have hsum := groupWeight available entries (·.2.slot) weight 0 hwithin
  have hcap := groupCapacity available entries (·.2.slot) weight capacity 0 (by
    intro slot hm
    simpa [weight, capacity, Optimality.usedVolume, gridLayout, List.map_map, Function.comp_def] using
      Optimality.layout_volume_fits _ _ (gridGroups_fit fit slot hm))
  rw [hsum] at hcap
  have hload := sumWeight_le entries ((gridLoad ∘ Prod.snd) ∘ Prod.fst) weight (by
    intro entry hm
    obtain ⟨_, _, ⟨_, hrotation⟩, _⟩ := hadmit entry hm
    exact List.min?_getD_le_of_mem (List.mem_map_of_mem (f := volume ∘ Prod.snd) hrotation))
  rw [← List.map_map, hcopies] at hload
  exact Nat.le_trans hload hcap

private def fitsAtOrigin (stock : Stock) (orientation : String × Axes) : Bool :=
  decide (Fits stock ⟨"", ⟨0, 0, 0⟩, orientation.2, orientation.1⟩)

private theorem gridOversize {rows : List DemandRow} {available : List StockRow}
    {plan : List (Option ExactGrid.Placement)} (hp : GridPlan available (copies rows) plan)
    (complete : none ∉ plan) :
    ∀ item ∈ copies rows, ∃ row ∈ available, ∃ orientation ∈ item.2.demand.orientations,
      fitsAtOrigin row.stock orientation = true := by
  obtain ⟨hcopies, hadmit⟩ := gridTagged_complete hp complete
  intro item hm
  rw [← hcopies] at hm
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hm
  obtain ⟨stock, hstock, ⟨_, horientation⟩, hfit⟩ := hadmit entry he
  have hmem : stock ∈ available.map StockRow.stock := List.mem_of_getElem? hstock
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hmem
  refine ⟨row, hr, _, horientation, ?_⟩
  apply decide_eq_true
  unfold Fits AxisFits at hfit ⊢
  dsimp only
  obtain ⟨⟨hx, hxr, hxb⟩, ⟨hy, hyr, hyb⟩, hz, hzr, hzb⟩ := hfit
  exact ⟨⟨hx, hxr, by omega⟩, ⟨hy, hyr, by omega⟩, hz, hzr, by omega⟩

def CompleteGrid (rows : List DemandRow) (available : List StockRow)
    (plan : List (Option ExactGrid.Placement)) : Prop :=
  GridPlan available (copies rows) plan ∧ none ∉ plan ∧ (evaluateGrid rows available plan).isSome = true

private def noSkips : List (Option α) → Bool
  | [] => true
  | choice :: rest => choice.isSome && noSkips rest

private theorem noSkips_iff (plan : List (Option α)) : noSkips plan = true ↔ none ∉ plan := by
  induction plan with
  | nil => simp [noSkips]
  | cons choice rest ih => cases choice <;> simp [noSkips, ih]

private def anyCompleteGrid (rows : List DemandRow) (available : List StockRow) : Bool :=
  anyChoices (gridChoices rows available) fun plan => noSkips plan && (evaluateGrid rows available plan).isSome

private theorem anyCompleteGrid_iff {rows : List DemandRow} {available : List StockRow} :
    anyCompleteGrid rows available = true ↔ ∃ plan, CompleteGrid rows available plan := by
  simp only [anyCompleteGrid, anyChoices_iff, CompleteGrid, Bool.and_eq_true, noSkips_iff]
  exact ⟨fun ⟨plan, hp, hc, hf⟩ => ⟨plan, gridChoices_sound hp, hc, hf⟩,
    fun ⟨plan, hp, hc, hf⟩ => ⟨plan, gridPlan_covered hp, hc, hf⟩⟩

def checkInfeasibleGrid (rows : List DemandRow) (stock : List StockRow) (witness : InfeasibilityWitness) : Bool :=
  let capacity := volume ∘ Stock.bounds ∘ StockRow.stock
  match witness with
  | .oversize => oversizeWitness rows stock fun row source =>
    !(row.demand.orientations.any (fitsAtOrigin source.stock))
  | .inventory => stock.all (·.stock.limit.isSome) && inventoryCapacity stock capacity < demandTotal rows gridLoad
  | .exhaustive =>
    let count := (rows.map (·.demand.quantity)).sum
    if count > 128 then false else
      let total := slotTotal count stock capacity
      if slotTotal count stock (fun _ => 1) > 65_536 || total > 65_536 then false else
        let combinations : Nat := (rows.map fun row => (1 + total * row.demand.orientations.length) ^
          row.demand.quantity).prod
        if combinations > 65_536 then false else !anyCompleteGrid rows (slots rows stock)

/-- An area or placement certificate on the sheet grid (the Z extent is one). -/
def checkInfeasible2D := checkInfeasibleGrid

/-- A volume or placement certificate on the cuboid grid. -/
def checkInfeasible3D := checkInfeasibleGrid

theorem infeasibleGrid_sound (rows : List DemandRow) (stock : List StockRow) (witness : InfeasibilityWitness)
    (h : checkInfeasibleGrid rows stock witness = true) :
    ¬ ∃ plan, CompleteGrid rows (slots rows stock) plan := by
  rintro ⟨plan, hp, hc, hf⟩
  cases witness with
  | oversize =>
    obtain ⟨item, hm, hfit⟩ := oversizeWitness_item h
    obtain ⟨row, hr, orientation, ho, hok⟩ := gridOversize hp hc item hm
    have fits := List.any_eq_true.mpr ⟨orientation, ho, hok⟩
    simpa [fits] using hfit row hr
  | inventory =>
    simp only [checkInfeasibleGrid, Bool.and_eq_true, decide_eq_true_eq] at h
    have load := gridInventory hp hc hf
    rw [sum_copies] at load
    exact Nat.not_lt_of_ge (Nat.le_trans load (slots_capacity_le rows stock _ h.1)) h.2
  | exhaustive =>
    have complete := anyCompleteGrid_iff.mpr ⟨plan, hp, hc, hf⟩
    simp [checkInfeasibleGrid, complete] at h

example :
    let size : Axes := ⟨2, 1, 1⟩
    let rows : List DemandRow := [⟨⟨"cut", size, 1_000_000, [("identity", size)]⟩, 1, 0, 0⟩]
    let source : StockRow := ⟨⟨"bar", size, size, 0, some 1⟩, 0, {}, none⟩
    let unavailable := { source with stock := { source.stock with limit := some 0 } }
    let unlimited := { source with stock := { source.stock with limit := none } }
    [checkInfeasible1D, checkInfeasibleGrid].all (fun check =>
      check rows [unavailable] .oversize && check rows [source] .inventory &&
      !check rows [unlimited] .inventory && !check rows [unlimited] .exhaustive) = true := by decide

inductive OpenProblem where
  | linear (rows : List DemandRow) (stock : StockRow)
  | grid (objective : PackingObjective) (rows : List DemandRow) (stock : StockRow)

def OpenProblem.objective : OpenProblem → PackingObjective
  | .linear .. => .open_dimension_x
  | .grid objective .. => objective

def OpenProblem.stock : OpenProblem → StockRow
  | .linear _ stock | .grid _ _ stock => stock

private def axisChoices (objective : PackingObjective) (axis upper : Nat) : List Nat :=
  if objective.axes.contains axis then List.range' 1 upper else [upper]

private def admissibleAxis (objective : PackingObjective) (axis upper size : Nat) : Prop :=
  if objective.axes.contains axis then 0 < size ∧ size ≤ upper else size = upper

private theorem mem_axisChoices (objective : PackingObjective) (axis upper size : Nat) :
    size ∈ axisChoices objective axis upper ↔ admissibleAxis objective axis upper size := by
  by_cases openAxis : axis ∈ objective.axes
  · simp only [axisChoices, admissibleAxis, List.contains_iff_mem, openAxis, ite_true, List.mem_range'_1]
    omega
  · simp [axisChoices, admissibleAxis, openAxis]

/-- Fixed axes retain their original sizes, while open axes range from one through the source cap. -/
def OpenProblem.Allows (problem : OpenProblem) (size : Axes) : Prop :=
  admissibleAxis problem.objective 0 problem.stock.stock.extent.x size.x ∧
  admissibleAxis problem.objective 1 problem.stock.stock.extent.y size.y ∧
  admissibleAxis problem.objective 2 problem.stock.stock.extent.z size.z

private def openSizes (problem : OpenProblem) : List Axes :=
  let upper := problem.stock.stock.extent
  let xs := axisChoices problem.objective 0 upper.x
  let ys := axisChoices problem.objective 1 upper.y
  let zs := axisChoices problem.objective 2 upper.z
  xs.flatMap fun x => ys.flatMap fun y => zs.map fun z => ⟨x, y, z⟩

private theorem mem_openSizes (problem : OpenProblem) (size : Axes) :
    size ∈ openSizes problem ↔ problem.Allows size := by
  cases size
  simp only [openSizes, OpenProblem.Allows, List.mem_flatMap, List.mem_map, Axes.mk.injEq, mem_axisChoices]
  constructor
  · rintro ⟨_, hx, _, hy, _, hz, rfl, rfl, rfl⟩
    exact ⟨hx, hy, hz⟩
  · rintro ⟨hx, hy, hz⟩
    exact ⟨_, hx, _, hy, _, hz, rfl, rfl, rfl⟩

private def openSizeCount (problem : OpenProblem) : Nat :=
  let size := problem.stock.stock.extent
  let objective := problem.objective
  (([size.x, size.y, size.z].zipIdx.map fun (cap, axis) =>
    if objective.axes.contains axis then cap else 1)).prod

private def clipPiece (size : Axes) (defect : Piece) : Option Piece :=
  let width := min defect.extent.x (size.x - defect.origin.x)
  let height := min defect.extent.y (size.y - defect.origin.y)
  if width == 0 || height == 0 then none else
    some { defect with extent := { defect.extent with x := width, y := height } }

private def openStock (problem : OpenProblem) (size : Axes) : List StockRow :=
  let row := problem.stock
  let limit := row.stock.limit.getD 1
  let trim := row.sheet.trim
  let bounds := match problem with
    | .linear .. => {size with x := size.x - (row.stock.extent.x - row.stock.bounds.x)}
    | .grid .. => size
  if limit == 0 || bounds.x == 0 || trim.trim_left + trim.trim_right ≥ size.x ||
      trim.trim_top + trim.trim_bottom ≥ size.y || size.z == 0 then [] else
    let stock := { row.stock with extent := size, bounds := bounds, limit := some 1 }
    let sheet := { row.sheet with defects := row.sheet.defects.filterMap (clipPiece size) }
    [{ row with stock := stock, sheet := sheet }]

private def openFeasible (problem : OpenProblem) (size : Axes) : Bool :=
  match problem with
  | .linear rows _ => anyCompleteLinear rows (openStock problem size)
  | .grid _ rows _ => anyCompleteGrid rows (openStock problem size)

def CompleteOpen (problem : OpenProblem) (size : Axes) : Prop :=
  problem.Allows size ∧ match problem with
  | .linear rows _ => ∃ plan, CompleteLinear rows (openStock problem size) plan
  | .grid _ rows _ => ∃ plan, CompleteGrid rows (openStock problem size) plan

private theorem openFeasible_iff (problem : OpenProblem) (size : Axes) :
    problem.Allows size → (openFeasible problem size = true ↔ CompleteOpen problem size) := by
  intro allows
  cases problem <;> simp only [openFeasible, CompleteOpen, allows, true_and, anyCompleteLinear_iff,
    anyCompleteGrid_iff]

private def openTrialBudget (problem : OpenProblem) (size : Axes) : Bool :=
  let available := openStock problem size
  match problem with
  | .linear rows _ => searchBudget (List.replicate (copies rows).length (available.length + 1))
  | .grid _ rows _ => gridBudget rows available

/-- Check the incumbent, then exclude every allowed crop with a strictly smaller primary value. -/
def checkExactOpenDim (problem : OpenProblem) (candidate : Axes) : Bool :=
  let value := extentValue problem.objective candidate
  !problem.objective.axes.isEmpty && openSizeCount problem ≤ 65_536 &&
    (openSizes problem).contains candidate && openTrialBudget problem candidate &&
    openFeasible problem candidate && (openSizes problem).all (fun size =>
      !(extentValue problem.objective size < value) ||
        (openTrialBudget problem size && !openFeasible problem size))

theorem exactOpenDim_sound (problem : OpenProblem) (candidate : Axes)
    (h : checkExactOpenDim problem candidate = true) :
    CompleteOpen problem candidate ∧ ∀ size, CompleteOpen problem size →
      extentValue problem.objective candidate ≤ extentValue problem.objective size := by
  simp only [checkExactOpenDim, Bool.and_eq_true, List.contains_iff_mem, mem_openSizes,
    List.all_eq_true] at h
  refine ⟨(openFeasible_iff _ _ h.1.1.1.2).mp h.1.2, fun size hs => Nat.le_of_not_gt ?_⟩
  intro better
  have test := h.2 size hs.1
  have feasible := (openFeasible_iff _ _ hs.1).mpr hs
  simp [better, feasible] at test

private def modelOfDimension : Dimension → Model
  | .linear => .linear
  | .sheet => .sheet
  | .box => .box

private def readExactCandidate (dim : Dimension) (input output : Json) :
    Except String (Option (PackingObjective × ReadProblem × ReadProblem × OptScore)) := do
  let model := modelOfDimension dim
  unless ← checkOptimized model input output do return none
  let source ← input.getObjVal? "problem"
  let options ← input.getObjVal? "options"
  let objective ← readDefault options "objective" PackingObjective.bin_count
  let profits ← (← readDefault source "profits" ([] : List Json)).mapM readAmount
  let minima ← readDefault source "minimum_quantities" ([] : List Nat)
  let problem ← readProblem model (← source.getObjVal? "packing") profits minima
  let effective ← readProblem model (← output.getObjVal? "effective_problem") profits minima
  let stockIndices ← output.getObjValAs? (List Nat) "stock_indices"
  let demandIndices ← output.getObjValAs? (List (List Nat)) "demand_indices"
  let (cost, waste) ← checkReadback model effective (← output.getObjVal? "solution")
    stockIndices demandIndices
  let score := scoreFor problem.demands demandIndices.flatten stockIndices.length cost waste
  return some (objective, problem, effective, score)

/-- Verify an optimized knapsack solution and certify exact optimality over all feasible plans. -/
def checkExactKnapsackOutput (dim : Dimension) (input output : Json) : Except String Bool := do
  let some (objective, problem, _, score) ← readExactCandidate dim input output | return false
  unless objective == .knapsack do return false
  -- All competing packings must stay within exact binary64 cost and profit totals.
  unless ((slots problem.demands problem.stocks).map StockRow.cost).sum ≤ maxExactUnits &&
      maxProfit problem.demands ≤ maxExactUnits do return false
  match dim with
  | .linear => return checkExactKnapsack1D problem.demands problem.stocks score
  | .sheet | .box => return checkExactKnapsackGrid problem.demands problem.stocks score

/-- Verify an optimized 2D or 3D minimum-cost solution and exclude every cheaper complete packing. -/
def checkExactCostGridOutput (dim : Dimension) (input output : Json) : Except String Bool := do
  let some (objective, problem, _, score) ← readExactCandidate dim input output | return false
  unless objective == .total_cost do return false
  unless ((slots problem.demands problem.stocks).map StockRow.cost).sum ≤ maxExactUnits do
    return false
  match dim with
  | .sheet | .box => return checkExactCostGrid problem.demands problem.stocks score
  | .linear => throw "exact grid cost requires 2D or 3D"

private def readExactOpenDimCandidate (dim : Dimension) (input output : Json) :
    Except String (Option (OpenProblem × Axes × OptScore)) := do
  let some (objective, problem, effective, score) ← readExactCandidate dim input output | return none
  unless !objective.axes.isEmpty do return none
  let [sourceStock] := problem.stocks | return none
  let [effectiveStock] := effective.stocks | return none
  let openProblem := match dim with
    | .linear => OpenProblem.linear problem.demands sourceStock
    | .sheet | .box => OpenProblem.grid objective problem.demands sourceStock
  return some (openProblem, effectiveStock.stock.extent, score)

/-- Verify a complete optimized open-dimension solution and exclude every smaller feasible extent/area. -/
def checkExactOpenDimOutput (dim : Dimension) (input output : Json) : Except String Bool :=
  match readExactOpenDimCandidate dim input output with
  | .error error => .error error
  | .ok none => .ok false
  | .ok (some (problem, candidate, score)) =>
    .ok (score.missingRequested == 0 && checkExactOpenDim problem candidate)

/-- Acceptance certifies that the reported incumbent places all requests at a minimum extent. -/
theorem checkExactOpenDimOutput_complete (dim : Dimension) (input output : Json)
    (h : checkExactOpenDimOutput dim input output = .ok true) :
    ∃ problem candidate score,
      readExactOpenDimCandidate dim input output = .ok (some (problem, candidate, score)) ∧
      score.missingRequested = 0 ∧ CompleteOpen problem candidate ∧ ∀ size, CompleteOpen problem size →
        extentValue problem.objective candidate ≤ extentValue problem.objective size := by
  cases parsed : readExactOpenDimCandidate dim input output with
  | error error => simp [checkExactOpenDimOutput, parsed] at h
  | ok result =>
    rcases result with _ | ⟨problem, candidate, score⟩
    · simp [checkExactOpenDimOutput, parsed] at h
    · have accepted : score.missingRequested = 0 ∧ checkExactOpenDim problem candidate = true := by
        simpa [checkExactOpenDimOutput, parsed, Bool.and_eq_true] using h
      exact ⟨problem, candidate, score, rfl, accepted.1, exactOpenDim_sound _ _ accepted.2⟩

/-- Verify an infeasibility witness (`oversize`, `inventory`, or `exhaustive`) for a packing job. -/
def checkInfeasibleOutput (dim : Dimension) (problem witnessJson : Json) : Except String Bool := do
  let model := modelOfDimension dim
  let parsed ← readProblem model problem
  let witness ← match witnessJson.getObjVal? "witness" with
    | .ok value => fromJson? (α := InfeasibilityWitness) value
    | .error _ => fromJson? (α := InfeasibilityWitness) witnessJson
  match dim with
  | .linear => return checkInfeasible1D parsed.demands parsed.stocks witness
  | .sheet => return checkInfeasible2D parsed.demands parsed.stocks witness
  | .box => return checkInfeasible3D parsed.demands parsed.stocks witness

run_cmd do
  let input ← ofExcept <| Json.parse r#"{
    "problem":{"packing":{"stock":[{"name":"bar","length":4}],
      "demands":[{"name":"cut","length":1,"quantity":3}]}},
    "options":{"objective":"open_dimension_x"}}"#
  let output ← ofExcept <| Json.parse r#"{
    "effective_problem":{"stock":[{"name":"bar","length":3,"available":1}],
      "demands":[{"name":"cut","length":1,"quantity":3}]},
    "stock_indices":[],"demand_indices":[],
    "solution":{"stock_count":0,"layouts":[],"total_cost":0,"total_waste":0,
      "unplaced":[{"name":"cut","length":1},{"name":"cut","length":1},{"name":"cut","length":1}]},
    "report":{"objective":"open_dimension_x","evaluations":1,"packing_states":0,
      "search_truncated":false,"open_extents":[3],"primary_optimal":false,"primary_bound":3,
      "selected_quantities":[0],"complete":false,"minimums_satisfied":true,"total_profit":0,
      "primary_value":3,"bound_is_upper":false}}"#
  let optimized ← ofExcept <| checkOptimized1D input output
  let accepted ← ofExcept <| checkExactOpenDimOutput .linear input output
  let some (problem, candidate, score) ← ofExcept (readExactOpenDimCandidate .linear input output)
    | throwError "expected the open-dimension readback to pass"
  unless optimized && score.missingRequested == 3 && checkExactOpenDim problem candidate && !accepted do
    throwError "incomplete incumbent at the minimum extent was not correctly rejected"

run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  let guarantees := [
    ``rank_irrefl,
    ``rank_trans,
    ``rank_tie,
    ``profit_rank_reverses,
    ``sumWeight_le,
    ``count_copies,
    ``selectedProfit_le,
    ``better_of_higher_profit,
    ``zipFirst_sublist,
    ``anyChoices_iff,
    ``evaluateLinear_profit,
    ``anyLinear_iff,
    ``exactKnapsack1D_sound,
    ``gridPlan_covered,
    ``gridTagged_sublist,
    ``evaluateGrid_profit,
    ``anyGrid_detects,
    ``gridChoice_admitted,
    ``gridChoices_sound,
    ``anyGrid_iff,
    ``exactKnapsackGrid_sound,
    ``exactCostGrid_sound,
    ``ceilDiv_le,
    ``count_bound_sound,
    ``minimum_cost_bound_sound,
    ``open_bound_sound,
    ``linear_open_bound_sound,
    ``nested_height_bound,
    ``sumPartition,
    ``groupWeight,
    ``groupCapacity,
    ``linearPlan_bounds,
    ``linearGroups_fit,
    ``linearInventory,
    ``mem_le_sum,
    ``linearOversize,
    ``anyCompleteLinear_iff,
    ``slot_has_stock,
    ``oversizeWitness_item,
    ``sum_copies,
    ``sum_slots,
    ``slots_capacity_le,
    ``infeasible1D_sound,
    ``gridTagged_complete,
    ``nested_column_bound,
    ``knapsack_bound_sound,
    ``gridGroups_fit,
    ``gridInventory,
    ``gridOversize,
    ``noSkips_iff,
    ``anyCompleteGrid_iff,
    ``infeasibleGrid_sound,
    ``mem_axisChoices,
    ``mem_openSizes,
    ``openFeasible_iff,
    ``exactOpenDim_sound,
    ``checkExactOpenDimOutput_complete
  ]
  for guarantee in guarantees do
    for axiomName in ← Lean.collectAxioms guarantee do
      unless allowed.contains axiomName do
        throwError "unexpected axiom {axiomName} in {guarantee}"

end Packing.Optimization
