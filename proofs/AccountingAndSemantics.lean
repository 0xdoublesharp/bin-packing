import Staged
import Saw
import Loading
import Optimality

set_option warningAsError true

namespace Packing.Semantics

open Lean

private theorem limit_iff (limit : Option Nat) (value : Nat) :
    Indexed.limitFits limit value = true ↔ ∀ cap, limit = some cap → value ≤ cap := by
  cases limit <;> simp [Indexed.limitFits]

/-- Every occurrence in the production sequence has completed all earlier demand rows in its group. -/
theorem checkGroups_sound {groups : List (Option Nat)} {demands : List Demand}
    {produced sequence : List Nat} (checked : Staged.checkGroups groups demands produced sequence = true)
    {prior suffix : List Nat} {current earlier group : Nat} {demand : Demand}
    (occurs : sequence = prior ++ current :: suffix)
    (member : groups[current]?.join = some group) (before : earlier < current)
    (earlierMember : groups[earlier]? = some (some group))
    (source : demands[earlier]? = some demand) :
    (prior.reverse ++ produced).count earlier = demand.quantity := by
  subst sequence
  induction prior generalizing produced with
  | nil =>
    simp only [List.nil_append, Staged.checkGroups, member, Bool.and_eq_true,
      List.all_eq_true] at checked
    have indexed : ((demand, some group), earlier) ∈ ((demands.zip groups).take current).zipIdx := by
      apply List.mk_mem_zipIdx_iff_getElem?.mpr
      rw [List.getElem?_take_of_lt before, List.getElem?_zip_eq_some]
      exact ⟨source, earlierMember⟩
    simpa using checked.1 _ indexed
  | cons head tail ih =>
    simp only [List.cons_append, Staged.checkGroups, Bool.and_eq_true] at checked
    simpa [List.reverse_cons, List.append_assoc] using ih checked.2

/-- The checker allows one terminal finishing stage in the specified non-exact modes. -/
def effectiveStageDepth (rules : Staged.Rules) (first : Staged.Axis) (tree : Staged.Tree) : Nat :=
  let blocks := tree.stageBlocks first none 0
  let deepest := (blocks.map Staged.StageBlock.stage).foldl max 0
  let finishingMax := match rules.cut_type with
    | .non_exact => 1
    | .roadef2018 => 2
    | _ => 0
  let discounted := deepest != 0 && (blocks.filter (fun block => block.stage == deepest)).all
    (fun block => decide (0 < block.demands.length ∧ block.demands.length ≤ finishingMax ∧
      block.wasteCount ≤ 1))
  deepest - if discounted then 1 else 0

/-- The designated first axis is permitted, every waste leaf meets both minimum side lengths,
and every declared maximum bounds the effective (finishing-adjusted) stage depth. -/
theorem checkStages_sound {rules : Staged.Rules} {first : Staged.Axis}
    {root : Staged.Region} {tree : Staged.Tree}
    (checked : Staged.checkStages rules first root tree = true) :
    (match rules.first_axis with
      | .any => True
      | .vertical => first = .vertical
      | .horizontal => first = .horizontal) ∧
    (∀ region ∈ tree.wasteRegions,
      rules.minimum_waste_length ≤ region.width ∧ rules.minimum_waste_length ≤ region.height) ∧
    ∀ cap, rules.max_stages = some cap → effectiveStageDepth rules first tree ≤ cap := by
  unfold Staged.checkStages at checked
  have ⟨other, depth⟩ := Bool.and_eq_true_iff.mp checked
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at other
  refine ⟨?_, other.2, (limit_iff _ _).mp depth⟩
  have firstOk := other.1.1.1.1
  cases h : rules.first_axis with
  | any => trivial
  | vertical => simpa [Staged.FirstAxis.permits, h] using firstOk
  | horizontal => simpa [Staged.FirstAxis.permits, h] using firstOk

/-- The list is in checker order (top to bottom), so its strict prior is the load above. -/
theorem checkWeightsAbove_iff (items : List (Option Nat × Nat)) (above : Nat) :
    Loading.checkWeightsAbove items above = true ↔
      ∀ i limit weight, items[i]? = some (some limit, weight) →
        above + ((items.take i).map Prod.snd).sum ≤ limit := by
  induction items generalizing above with
  | nil => simp [Loading.checkWeightsAbove]
  | cons item rest ih =>
    rcases item with ⟨limit, mass⟩
    rw [Loading.checkWeightsAbove, Bool.and_eq_true, limit_iff, ih]
    constructor
    · rintro ⟨head, tail⟩ (i | i) cap weight h
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
        simpa using head cap h.1
      · simpa [List.take_succ_cons, Nat.add_assoc, List.getElem?_cons_succ] using
          tail i cap weight (by simpa using h)
    · intro h
      refine ⟨fun cap hcap => ?_, fun i cap weight hi => ?_⟩
      · simpa using h 0 cap mass (by simp [hcap])
      · simpa [List.take_succ_cons, Nat.add_assoc] using
          h (i + 1) cap weight (by simpa using hi)

/-- Both positive denominators can be cleared without rounding or changing the inequality. -/
theorem density_sound (column : Loading.Column) (density : Loading.Density)
    (widthPositive : 0 < column.width) (depthPositive : 0 < column.depth)
    (checked : decide (0 < density.denominator ∧
      column.weight * density.denominator ≤ density.numerator * column.width * column.depth) = true) :
    (column.weight : Rat) / ((column.width : Rat) * (column.depth : Rat)) ≤
      (density.numerator : Rat) / (density.denominator : Rat) := by
  obtain ⟨denPositive, fits⟩ := of_decide_eq_true checked
  let floor : Rat := column.width * (column.depth : Rat)
  let den : Rat := density.denominator
  have hfloor : 0 < floor := Rat.mul_pos (Rat.natCast_pos.mpr widthPositive)
    (Rat.natCast_pos.mpr depthPositive)
  have hden : 0 < den := Rat.natCast_pos.mpr denPositive
  change (column.weight : Rat) / floor ≤ (density.numerator : Rat) / den
  apply Rat.le_of_mul_le_mul_right (c := den * floor) _ (Rat.mul_pos hden hfloor)
  have left : (column.weight : Rat) / floor * (den * floor) = (column.weight : Rat) * den := by
    rw [Rat.mul_comm den floor, ← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hfloor)]
  rw [left, ← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hden)]
  have cross : (↑(column.weight * density.denominator) : Rat) ≤
      ↑(density.numerator * (column.width * column.depth)) :=
    Rat.natCast_le_natCast.mpr (by simpa [Nat.mul_assoc] using fits)
  simpa [floor, den, Rat.natCast_mul] using cross

def Apart (x width y depth : Nat) : Prop := x + width ≤ y ∨ y + depth ≤ x

def FloorApart (a b : Loading.FloorRect) : Prop :=
  Apart a.x a.width b.x b.width ∨ Apart a.z a.depth b.z b.depth

/-- Separation of two intervals when the first is translated by a rational distance. -/
def ShiftApart (start size other otherSize : Nat) (distance : Rat) : Prop :=
  (start : Rat) + size + distance ≤ (other : Rat) ∨
    (other : Rat) + otherSize ≤ (start : Rat) + distance

def FloorApartAfter (a b : Loading.FloorRect) (x z : Rat) : Prop :=
  ShiftApart a.x a.width b.x b.width x ∨ ShiftApart a.z a.depth b.z b.depth z

/-- Positive-axis translation by any nonnegative distance keeps the footprints disjoint.
Increasing-coordinate modes use the initial floor separation checked by the layout checker. -/
def UnloadingClear (rule : Loading.Delivery) (early late : Loading.FloorRect) : Prop :=
  match rule with
  | .none => True
  | .only_x_movements => ∀ distance, 0 ≤ distance → FloorApartAfter early late distance 0
  | .only_z_movements => ∀ distance, 0 ≤ distance → FloorApartAfter early late 0 distance
  | .increasing_x => late.x ≤ early.x ∧
    (FloorApart early late → ∀ distance, 0 ≤ distance → FloorApartAfter early late distance 0)
  | .increasing_z => late.z ≤ early.z ∧
    (FloorApart early late → ∀ distance, 0 ≤ distance → FloorApartAfter early late 0 distance)

private theorem shiftApart_zero {x w y d : Nat} (apart : Apart x w y d) :
    ShiftApart x w y d 0 := by
  simpa [ShiftApart, Apart, Rat.add_zero, ← Rat.natCast_add, Rat.natCast_le_natCast] using apart

private theorem shiftApart_behind {x w y d : Nat} {distance : Rat}
    (behind : y + d ≤ x) (forward : 0 ≤ distance) : ShiftApart x w y d distance := by
  apply Or.inr
  rw [← Rat.natCast_add]
  apply Rat.le_trans (Rat.natCast_le_natCast.mpr behind)
  have moved := (Rat.add_le_add_left (c := (x : Rat))).mpr forward
  rwa [Rat.add_zero] at moved

private theorem floorApart_after_x {early late : Loading.FloorRect}
    (clear : Apart late.z late.depth early.z early.depth ∨ late.x + late.width ≤ early.x)
    {distance : Rat} (forward : 0 ≤ distance) : FloorApartAfter early late distance 0 := by
  rcases clear with orthogonal | behind
  · exact Or.inr (shiftApart_zero (by unfold Apart at *; omega))
  · exact Or.inl (shiftApart_behind behind forward)

private theorem floorApart_after_z {early late : Loading.FloorRect}
    (clear : Apart late.x late.width early.x early.width ∨ late.z + late.depth ≤ early.z)
    {distance : Rat} (forward : 0 ≤ distance) : FloorApartAfter early late 0 distance := by
  rcases clear with orthogonal | behind
  · exact Or.inl (shiftApart_zero (by unfold Apart at *; omega))
  · exact Or.inr (shiftApart_behind behind forward)

private theorem deliveryPair_swap (rule : Loading.Delivery) (a b : Loading.Cargo) :
    Loading.deliveryPair rule a b = Loading.deliveryPair rule b a := by
  rcases Nat.lt_trichotomy a.groupId b.groupId with h | h | h
  · simp [Loading.deliveryPair, Nat.ne_of_lt h, Nat.ne_of_gt h, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
  · simp [Loading.deliveryPair, h]
  · simp [Loading.deliveryPair, Nat.ne_of_lt h, Nat.ne_of_gt h, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]

private theorem deliveryPair_clear {rule : Loading.Delivery} {early late : Loading.Cargo}
    (order : early.groupId < late.groupId) (checked : Loading.deliveryPair rule early late = true)
    (widthPositive : 0 < early.footprint.width) (depthPositive : 0 < early.footprint.depth) :
    UnloadingClear rule early.footprint late.footprint := by
  cases rule <;> simp [Loading.deliveryPair, Nat.ne_of_lt order, order, UnloadingClear] at *
  · exact fun _ forward => floorApart_after_x (by unfold Apart; omega) forward
  · exact fun _ forward => floorApart_after_z (by unfold Apart; omega) forward
  · exact ⟨checked, fun apart _ forward => floorApart_after_x (by
      unfold FloorApart Apart at *
      omega) forward⟩
  · exact ⟨checked, fun apart _ forward => floorApart_after_z (by
      unfold FloorApart Apart at *
      omega) forward⟩

private theorem pairsAcrossColumns_pairwise (rule : Loading.Delivery)
    (columns : List (List Loading.Cargo)) (checked : Loading.pairsAcrossColumns rule columns = true) :
    columns.Pairwise (fun a b => ∀ x ∈ a, ∀ y ∈ b, Loading.deliveryPair rule x y = true) := by
  induction columns with
  | nil => exact .nil
  | cons head tail ih =>
    simp only [Loading.pairsAcrossColumns, Bool.and_eq_true, List.all_eq_true] at checked
    exact .cons (fun _ hy _ hx _ hz => checked.1 _ hx _ hy _ hz) (ih checked.2)

/-- Later-delivered cargo in distinct columns cannot obstruct the indicated unloading path.
The ordered-coordinate modes inherit initial separation from valid physical footprints. -/
theorem unloading_unblocked {rule : Loading.Delivery} {columns : List (List Loading.Cargo)}
    (checked : Loading.pairsAcrossColumns rule columns = true)
    {i j : Nat} {a b : List Loading.Cargo} (ha : columns[i]? = some a)
    (hb : columns[j]? = some b) (distinct : i ≠ j)
    {early late : Loading.Cargo} (he : early ∈ a) (hl : late ∈ b)
    (order : early.groupId < late.groupId)
    (widthPositive : 0 < early.footprint.width) (depthPositive : 0 < early.footprint.depth) :
    UnloadingClear rule early.footprint late.footprint := by
  apply deliveryPair_clear order _ widthPositive depthPositive
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  have pairwise := List.pairwise_iff_getElem.mp (pairsAcrossColumns_pairwise rule columns checked)
  by_cases h : i < j
  · exact pairwise i j hi hj h early he late hl
  · rw [deliveryPair_swap]
    exact pairwise j i hj hi (by omega) late hl early he

/-- Evaluation-count model for the optimization driver. Candidate validity is the backend contract. -/
structure BoundedSearchState (α : Type) where
  maxEvaluations : Nat
  evaluations : Nat
  truncated : Bool
  incumbent : α

structure Evaluation (α : Type) where
  candidate : α
  replaceIncumbent : Bool
  beamCandidates : Nat := 0
  backendTruncated : Bool := false

structure SearchResult (α : Type) where
  final : BoundedSearchState α
  steps : Nat := 0
  budgetDropped : Bool := false
  beamDropped : Bool := false

private def Evaluation.dropsBeamWork (value : Evaluation α) (beamWidth : Nat) : Bool :=
  decide (beamWidth < value.beamCandidates)

private def commitEvaluation (beamWidth : Nat) (state : BoundedSearchState α) (value : Evaluation α) :
    BoundedSearchState α :=
  { state with
    evaluations := state.evaluations + 1
    truncated := state.truncated || value.dropsBeamWork beamWidth || value.backendTruncated
    incumbent := if value.replaceIncumbent then value.candidate else state.incumbent }

private def runSearch (beamWidth : Nat) (plan : BoundedSearchState α → Option β) (evaluate : β → Evaluation α) :
    Nat → BoundedSearchState α → SearchResult α
  | fuel, state =>
    match plan state with
    | none => { final := state }
    | some request =>
      match fuel with
      | 0 => { final := { state with truncated := true }, budgetDropped := true }
      | fuel + 1 =>
        let value := evaluate request
        let rest := runSearch beamWidth plan evaluate fuel (commitEvaluation beamWidth state value)
        { rest with steps := rest.steps + 1, beamDropped := value.dropsBeamWork beamWidth || rest.beamDropped }

def boundedSearch (beamWidth : Nat) (plan : BoundedSearchState α → Option β) (evaluate : β → Evaluation α)
    (initial : BoundedSearchState α) : SearchResult α :=
  runSearch beamWidth plan evaluate (initial.maxEvaluations - initial.evaluations) initial

private def SearchInvariant (Valid : α → Prop) (initial : BoundedSearchState α)
    (fuel : Nat) (result : SearchResult α) : Prop :=
  result.steps ≤ fuel ∧
  result.final.evaluations = initial.evaluations + result.steps ∧
  result.final.maxEvaluations = initial.maxEvaluations ∧
  (result.budgetDropped = true → result.steps = fuel) ∧
  (initial.truncated = true ∨ result.budgetDropped = true ∨ result.beamDropped = true →
    result.final.truncated = true) ∧
  Valid result.final.incumbent

private theorem runSearch_invariant (Valid : α → Prop) (beamWidth : Nat)
    (plan : BoundedSearchState α → Option β)
    (evaluate : β → Evaluation α) (candidateValid : ∀ request, Valid (evaluate request).candidate)
    (fuel : Nat) (initial : BoundedSearchState α) (initialValid : Valid initial.incumbent) :
    SearchInvariant Valid initial fuel (runSearch beamWidth plan evaluate fuel initial) := by
  induction fuel generalizing initial with
  | zero => cases h : plan initial <;> simp [runSearch, h, SearchInvariant, initialValid]
  | succ fuel ih =>
    cases h : plan initial with
    | none => simp [runSearch, h, SearchInvariant, initialValid]
    | some request =>
      let value := evaluate request
      let next := commitEvaluation beamWidth initial value
      have nextValid : Valid next.incumbent := by
        simp only [next, commitEvaluation]
        split
        · exact candidateValid request
        · exact initialValid
      let result := runSearch beamWidth plan evaluate fuel next
      obtain ⟨steps, evaluations, sameBudget, exhausted, marked, valid⟩ := ih next nextValid
      rw [runSearch, h]
      change SearchInvariant Valid initial (fuel + 1)
        { result with steps := result.steps + 1, beamDropped := value.dropsBeamWork beamWidth || result.beamDropped }
      change result.steps ≤ fuel at steps
      change result.final.evaluations = initial.evaluations + 1 + result.steps at evaluations
      dsimp only [SearchInvariant]
      refine ⟨by omega, by omega, sameBudget, fun dropped => ?_, ?_, valid⟩
      · exact congrArg (· + 1) (exhausted dropped)
      · simp only [Bool.or_eq_true]
        rintro (already | budget | beam | beam) <;> apply marked
        · exact Or.inl (by simp [next, commitEvaluation, already])
        · exact Or.inr (Or.inl budget)
        · exact Or.inl (by simp [next, commitEvaluation, beam])
        · exact Or.inr (Or.inr beam)

/-- Every recursive step consumes one evaluation. A request at the cap or a beam drop
marks the result truncated, and an accepted replacement preserves the incumbent invariant. -/
theorem bounded_search_terminates_and_respects_budget (Valid : α → Prop) (beamWidth : Nat)
    (plan : BoundedSearchState α → Option β) (evaluate : β → Evaluation α)
    (initial : BoundedSearchState α) (withinBudget : initial.evaluations ≤ initial.maxEvaluations)
    (initialValid : Valid initial.incumbent)
    (candidateValid : ∀ request, Valid (evaluate request).candidate) :
    let result := boundedSearch beamWidth plan evaluate initial
    result.steps ≤ initial.maxEvaluations - initial.evaluations ∧
    result.final.evaluations = initial.evaluations + result.steps ∧
    result.final.evaluations ≤ result.final.maxEvaluations ∧
    result.final.maxEvaluations = initial.maxEvaluations ∧
    (result.budgetDropped = true → result.final.evaluations = initial.maxEvaluations) ∧
    (initial.truncated = true ∨ result.budgetDropped = true ∨ result.beamDropped = true →
      result.final.truncated = true) ∧
    Valid result.final.incumbent := by
  simp only [boundedSearch]
  obtain ⟨steps, evaluations, budget, exhausted, marked, valid⟩ :=
    runSearch_invariant Valid beamWidth plan evaluate candidateValid
      (initial.maxEvaluations - initial.evaluations) initial initialValid
  exact ⟨steps, evaluations, by omega, budget, fun dropped => by
    have used := exhausted dropped
    omega, marked, valid⟩

/-- Source data before the geometry decoder applies trim and edge relief. -/
structure InputStock where
  name : String
  size : Axes
  cost : Float
  kerf : Nat := 0
  trim : Nat := 0
  quantity : Option Nat := none

structure InputDemand where
  size : Axes
  quantity : Nat
  rotationMask : UInt8 := 63

def ValidCost (cost : Float) : Prop := cost.isFinite = true ∧ ¬cost < 0.0

def ValidStock1D (stock : InputStock) : Prop :=
  0 < stock.size.x ∧ stock.size.x ≤ 2^30 ∧ stock.kerf ≤ 2^30 ∧
    stock.trim < stock.size.x ∧ ValidCost stock.cost

def ValidDemand1D (demand : InputDemand) : Prop :=
  0 < demand.size.x ∧ demand.size.x ≤ 2^30 ∧
    0 < demand.quantity ∧ demand.quantity ≤ 2^32 - 1

def ValidSheet2D (sheet : InputStock) : Prop :=
  0 < sheet.size.x ∧ sheet.size.x ≤ 2^30 ∧
    0 < sheet.size.y ∧ sheet.size.y ≤ 2^30 ∧
    2 * sheet.kerf < min sheet.size.x sheet.size.y ∧ ValidCost sheet.cost

def ValidDemand2D (demand : InputDemand) : Prop :=
  ValidDemand1D demand ∧ 0 < demand.size.y ∧ demand.size.y ≤ 2^30

def ValidBin3D (bin : InputStock) : Prop :=
  0 < bin.size.x ∧ bin.size.x ≤ 2^15 ∧ 0 < bin.size.y ∧ bin.size.y ≤ 2^15 ∧
    0 < bin.size.z ∧ bin.size.z ≤ 2^15 ∧ ValidCost bin.cost ∧ bin.quantity ≠ some 0

def ValidDemand3D (demand : InputDemand) : Prop :=
  0 < demand.size.x ∧ demand.size.x ≤ 2^15 ∧
    0 < demand.size.y ∧ demand.size.y ≤ 2^15 ∧
    0 < demand.size.z ∧ demand.size.z ≤ 2^15 ∧
    0 < demand.quantity ∧ demand.quantity ≤ 2^32 - 1 ∧ demand.rotationMask ≠ 0

def ValidStock (dim : Dimension) : InputStock → Prop :=
  match dim with | .linear => ValidStock1D | .sheet => ValidSheet2D | .box => ValidBin3D

def ValidDemand (dim : Dimension) : InputDemand → Prop :=
  match dim with | .linear => ValidDemand1D | .sheet => ValidDemand2D | .box => ValidDemand3D

instance (dim : Dimension) (stock : InputStock) : Decidable (ValidStock dim stock) := by
  cases dim <;> unfold ValidStock ValidStock1D ValidSheet2D ValidBin3D ValidCost <;> infer_instance

instance (dim : Dimension) (demand : InputDemand) : Decidable (ValidDemand dim demand) := by
  cases dim <;> simp only [ValidDemand, ValidDemand1D, ValidDemand2D, ValidDemand3D] <;> infer_instance

def ValidInput (dim : Dimension) (stocks : List InputStock) (demands : List InputDemand) : Prop :=
  stocks ≠ [] ∧ demands ≠ [] ∧ (stocks.map InputStock.name).Nodup ∧
  (∀ stock ∈ stocks, ValidStock dim stock) ∧ (∀ demand ∈ demands, ValidDemand dim demand) ∧
  (demands.map InputDemand.quantity).sum ≤ 2^32 - 1

def checkValidInput (dim : Dimension) (stocks : List InputStock) (demands : List InputDemand) : Bool :=
  (!stocks.isEmpty && !demands.isEmpty && decide ((stocks.map InputStock.name).Nodup)) &&
  stocks.all (fun stock => decide (ValidStock dim stock)) &&
  demands.all (fun demand => decide (ValidDemand dim demand)) &&
  decide ((demands.map InputDemand.quantity).sum ≤ 2^32 - 1)

theorem checkValidInput_iff (dim : Dimension) (stocks : List InputStock) (demands : List InputDemand) :
    checkValidInput dim stocks demands = true ↔ ValidInput dim stocks demands := by
  simp [checkValidInput, ValidInput, Bool.and_eq_true, and_assoc]

theorem readDefault_absent_returns_fallback [FromJson α] {json : Json} {key : String} {fallback : α}
    (object : json.getObj? = .ok fields) (absent : fields.get? key = none) :
    readDefault json key fallback = .ok fallback := by
  unfold readDefault
  rw [object]
  change (match fields.get? key with
    | none => Except.ok (ε := String) fallback
    | some value => fromJson? value) = _
  rw [absent]

theorem readDefault_present_decodes [FromJson α] {json : Json} {key : String} {fallback : α}
    (object : json.getObj? = .ok fields) (present : fields.get? key = some value) :
    readDefault json key fallback = fromJson? value := by
  unfold readDefault
  rw [object]
  change (match fields.get? key with
    | none => Except.ok (ε := String) fallback
    | some value => fromJson? value) = _
  rw [present]

/-- Area on the physical sheet, with any edge-relief overhang clipped away. -/
def clippedLength (bound start size : Nat) : Nat := min (start + size) bound - start

def clippedSheetPiece (sheet : Axes) (piece : Piece) : Piece :=
  { piece with extent := ⟨clippedLength sheet.x piece.origin.x piece.extent.x,
    clippedLength sheet.y piece.origin.y piece.extent.y, piece.extent.z⟩ }

def usedSheetArea (sheet : Axes) (layout : Layout) : Nat :=
  (layout.pieces.map (fun piece =>
    let clipped := clippedSheetPiece sheet piece
    clipped.extent.x * clipped.extent.y)).sum

private theorem clippedLength_le_size (bound start size : Nat) :
    clippedLength bound start size ≤ size := by
  unfold clippedLength
  have := Nat.min_le_left (start + size) bound
  omega

private theorem clippedLength_fits {bound start size : Nat}
    (positive : 0 < clippedLength bound start size) :
    AxisFits start (clippedLength bound start size) bound bound := by
  unfold AxisFits clippedLength at *
  have := Nat.min_le_right (start + size) bound
  omega

private theorem clip_separated (sheet : Axes) {gap : Nat} {a b : Piece} (h : Separated gap a b) :
    Separated gap (clippedSheetPiece sheet a) (clippedSheetPiece sheet b) := by
  unfold Separated AxisSeparated at *
  dsimp [clippedSheetPiece]
  have ax := clippedLength_le_size sheet.x a.origin.x a.extent.x
  have bx := clippedLength_le_size sheet.x b.origin.x b.extent.x
  have ay := clippedLength_le_size sheet.y a.origin.y a.extent.y
  have by' := clippedLength_le_size sheet.y b.origin.y b.extent.y
  omega

private theorem sum_positive (measure : α → Nat) (values : List α) :
    ((values.filter (fun value => decide (0 < measure value))).map measure).sum =
      (values.map measure).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    by_cases h : 0 < measure head
    · simp [h, ih]
    · have zero : measure head = 0 := by omega
      simp [zero, ih]

private theorem usedSheetArea_fits {layout : Layout} {stock : Stock}
    (valid : layout.Valid stock) (unitDepth : stock.extent.z = 1)
    (zBound : stock.bounds.z = 1) :
    usedSheetArea stock.extent layout ≤ stock.extent.x * stock.extent.y := by
  let clipped := layout.pieces.map (clippedSheetPiece stock.extent)
  let inside := clipped.filter (fun piece => decide (0 < Optimality.volume piece.extent))
  let physicalStock := { stock with bounds := stock.extent }
  let physical : Layout := { layout with pieces := inside, linear := none }
  have placed : ∀ piece ∈ layout.pieces, piece.origin.z = 0 ∧ piece.extent.z = 1 := by
    intro piece hp
    have z := (valid.2.2.1 piece hp).2.2
    unfold AxisFits at z
    omega
  have fits : physical.Valid physicalStock := by
    refine ⟨valid.1, valid.2.1, ?_, ?_, by simp [physical]⟩
    · intro piece hp
      obtain ⟨hm, positive⟩ := List.mem_filter.mp hp
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨zero, one⟩ := placed original ho
      have volume := of_decide_eq_true positive
      simp only [clippedSheetPiece, Optimality.volume, one, Nat.mul_one] at volume
      have hx : 0 < clippedLength stock.extent.x original.origin.x original.extent.x := by
        by_cases h : clippedLength stock.extent.x original.origin.x original.extent.x = 0
        · simp [h] at volume
        · omega
      have hy : 0 < clippedLength stock.extent.y original.origin.y original.extent.y := by
        by_cases h : clippedLength stock.extent.y original.origin.y original.extent.y = 0
        · simp [h] at volume
        · omega
      exact ⟨clippedLength_fits hx, clippedLength_fits hy, by
        simp [AxisFits, physicalStock, clippedSheetPiece, unitDepth, zero, one]⟩
    · exact ((List.pairwise_map.mpr (valid.2.2.2.1.imp (clip_separated stock.extent))).filter _)
  have area : Optimality.usedVolume physical = usedSheetArea stock.extent layout := by
    unfold Optimality.usedVolume usedSheetArea
    change (inside.map (Optimality.volume ∘ Piece.extent)).sum = _
    calc
      _ = (clipped.map (Optimality.volume ∘ Piece.extent)).sum :=
        sum_positive (Optimality.volume ∘ Piece.extent) clipped
      _ = _ := by
        simp only [clipped, List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro piece hp
        simp [clippedSheetPiece, Optimality.volume, (placed piece hp).2]
  simpa [area, physicalStock, Optimality.volume, unitDepth] using
    Optimality.layout_volume_fits physicalStock physical fits

structure PricedMaterial where
  stock : Stock
  cost : Float

structure AccountingRow where
  layout : Layout
  used : Nat
  waste : Nat
  cost : Float

structure Accounting where
  stocks : List PricedMaterial
  demands : List Demand
  rows : List AccountingRow
  shortages : List Shortage
  layoutCount : Nat
  totalWaste : Nat
  totalCost : Float

def Accounting.certificate (report : Accounting) : Certificate :=
  ⟨report.stocks.map PricedMaterial.stock, report.demands, report.rows.map AccountingRow.layout,
    report.shortages, report.layoutCount⟩

def materialCapacity (dim : Dimension) (stock : Stock) : Nat :=
  match dim with
  | .linear => stock.bounds.x
  | .sheet => stock.extent.x * stock.extent.y
  | .box => Optimality.volume stock.extent

def materialUsed (dim : Dimension) (stock : Stock) (layout : Layout) : Nat :=
  match dim with
  | .linear => linearLength stock.gap (layout.pieces.map (·.extent.x))
  | .sheet => usedSheetArea stock.extent layout
  | .box => Optimality.usedVolume layout

private def checkExtent (dim : Dimension) (stock : Stock) (row : AccountingRow) : Bool :=
  match dim with
  | .linear =>
    row.layout.linear.any (fun summary => summary.used == row.used && summary.waste == row.waste) &&
      decide (stock.bounds.x ≤ stock.extent.x)
  | .sheet => decide (stock.extent.z = 1 ∧ stock.bounds.z = 1)
  | .box => decide (stock.bounds = stock.extent)

private instance (cost : Float) : Decidable (ValidCost cost) := by
  unfold ValidCost
  infer_instance

private def checkAccountingRow (dim : Dimension) (row : AccountingRow) (source : PricedMaterial) :
    Bool :=
  row.layout.check source.stock && checkExtent dim source.stock row &&
    decide (row.used = materialUsed dim source.stock row.layout ∧
      row.waste = materialCapacity dim source.stock - row.used) &&
    decide (row.cost = source.cost ∧ ValidCost source.cost)

/-- Native totals use binary64 addition in emitted layout order. -/
def sumPrices (dim : Dimension) (prices : List Float) : Float :=
  let zero : Float := match dim with | .linear => 0.0 | _ => -0.0
  prices.foldl (· + ·) zero

def sumCost (dim : Dimension) (rows : List AccountingRow) : Float :=
  sumPrices dim (rows.map AccountingRow.cost)

def checkAccounting (dim : Dimension) (report : Accounting) : Bool :=
  report.certificate.check &&
  report.rows.all (fun row => report.stocks.any (checkAccountingRow dim row)) &&
  (report.totalWaste == (report.rows.map AccountingRow.waste).sum) &&
  (report.totalCost == sumCost dim report.rows)

def AccountedRow (dim : Dimension) (stocks : List PricedMaterial) (row : AccountingRow) : Prop :=
  ∃ source ∈ stocks,
    row.layout.Valid source.stock ∧
    row.used = materialUsed dim source.stock row.layout ∧
    row.used ≤ materialCapacity dim source.stock ∧
    row.used + row.waste = materialCapacity dim source.stock ∧
    row.cost = source.cost ∧ ValidCost source.cost ∧
    match dim with
    | .linear => ∃ summary, row.layout.linear = some summary ∧
        summary.used = row.used ∧ summary.remaining = row.waste ∧ summary.waste = row.waste ∧
        row.used + row.waste + (source.stock.extent.x - source.stock.bounds.x) = source.stock.extent.x
    | _ => True

private theorem accounting_row_sound (dim : Dimension) {row : AccountingRow} {source : PricedMaterial}
    (checked : checkAccountingRow dim row source = true) :
    AccountedRow dim [source] row := by
  simp only [checkAccountingRow, Bool.and_eq_true, Layout.check_iff, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨valid, extent⟩, used, waste⟩, cost, costValid⟩ := checked
  have fits : row.used ≤ materialCapacity dim source.stock := by
    rw [used]
    cases dim with
    | linear =>
      cases h : row.layout.linear with
      | none => simp [checkExtent, h] at extent
      | some summary =>
        have accounting := valid.2.2.2.2 summary h
        simp only [materialCapacity, materialUsed]
        omega
    | sheet =>
      simp only [checkExtent, decide_eq_true_eq] at extent
      exact usedSheetArea_fits valid extent.1 extent.2
    | box =>
      simp only [checkExtent, decide_eq_true_eq] at extent
      simpa [materialUsed, materialCapacity, extent] using
        Optimality.layout_volume_fits source.stock row.layout valid
  have conserved : row.used + row.waste = materialCapacity dim source.stock := by omega
  refine ⟨source, by simp, valid, used, fits, conserved, cost, costValid, ?_⟩
  cases dim with
  | linear =>
    cases h : row.layout.linear with
    | none => simp [checkExtent, h] at extent
    | some summary =>
      simp [checkExtent, h] at extent
      have accounting := valid.2.2.2.2 summary h
      exact ⟨summary, rfl, extent.1.1, accounting.2.2.symm.trans extent.1.2, extent.1.2, by
        simp only [materialCapacity] at conserved
        omega⟩
  | sheet | box => trivial

/-- The source stock consumed by each layout, in layout order. -/
def Accounting.sources (dim : Dimension) (report : Accounting) : Option (List PricedMaterial) :=
  report.rows.mapM (fun row => report.stocks.find? (checkAccountingRow dim row))

def AccountingSound (dim : Dimension) (report : Accounting) : Prop :=
  report.certificate.Valid ∧
  (∀ row ∈ report.rows, AccountedRow dim report.stocks row) ∧
  report.totalWaste = (report.rows.map AccountingRow.waste).sum ∧
  ∃ sources, report.sources dim = some sources ∧
    (report.rows.map AccountingRow.used).sum + report.totalWaste =
      (sources.map (materialCapacity dim ∘ PricedMaterial.stock)).sum ∧
    (report.totalCost == sumPrices dim (sources.map PricedMaterial.cost)) = true

private theorem source_sums (dim : Dimension) (stocks : List PricedMaterial) (rows : List AccountingRow)
    (checked : ∀ row ∈ rows, stocks.any (checkAccountingRow dim row) = true) :
    ∃ sources, rows.mapM (fun row => stocks.find? (checkAccountingRow dim row)) = some sources ∧
      (rows.map AccountingRow.used).sum + (rows.map AccountingRow.waste).sum =
        (sources.map (materialCapacity dim ∘ PricedMaterial.stock)).sum ∧
      rows.map AccountingRow.cost = sources.map PricedMaterial.cost := by
  induction rows with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons row rest ih =>
    obtain ⟨sources, readRest, material, costs⟩ :=
      ih (fun row member => checked row (List.mem_cons_of_mem _ member))
    have existsSource := checked row (by simp)
    cases found : stocks.find? (checkAccountingRow dim row) with
    | none =>
      have empty := List.find?_eq_none.mp found
      obtain ⟨source, member, accepted⟩ := List.any_eq_true.mp existsSource
      simp [empty source member] at accepted
    | some source =>
      have rowOk := accounting_row_sound dim (List.find?_some found)
      obtain ⟨actual, member, _, _, _, conserved, price, _⟩ := rowOk
      have same := List.mem_singleton.mp member
      subst actual
      refine ⟨source :: sources, ?_, ?_, ?_⟩
      · simp [List.mapM_cons, found, readRest]
      · simp only [List.map_cons, List.sum_cons, Function.comp_apply]
        omega
      · simp [price, costs]

/-- Accepted summaries conserve material and price each layout at its source cost. -/
theorem accounting_sound (dim : Dimension) {report : Accounting}
    (checked : checkAccounting dim report = true) : AccountingSound dim report := by
  simp only [checkAccounting, Bool.and_eq_true, Certificate.check_iff, List.all_eq_true] at checked
  obtain ⟨⟨⟨valid, rows⟩, waste⟩, cost⟩ := checked
  have totalWaste := beq_iff_eq.mp waste
  refine ⟨valid, ?_, totalWaste, ?_⟩
  · intro row member
    obtain ⟨source, hs, accepted⟩ := List.any_eq_true.mp (rows row member)
    obtain ⟨actual, ha, proof⟩ := accounting_row_sound dim accepted
    have eq : actual = source := List.mem_singleton.mp ha
    exact ⟨source, hs, eq ▸ proof⟩
  · obtain ⟨sources, read, material, prices⟩ := source_sums dim report.stocks report.rows rows
    refine ⟨sources, read, ?_, ?_⟩
    · rwa [totalWaste]
    · rwa [← prices]

private def readNumericCost (json : Json) : Except String Float := do
  let cost := (← json.getNum?).toFloat
  unless cost.isFinite do throw "cost exceeds the finite binary64 range"
  return cost

def readAccounting (dim : Dimension) (problem solution : Json) : Except String Accounting := do
  let certificate ← readCertificate dim problem solution
  let (stockKey, usedKey, wasteKey, totalKey) := match dim with
    | .linear => ("stock", "used_length", "waste", "total_waste")
    | .sheet => ("sheets", "used_area", "waste_area", "total_waste_area")
    | .box => ("bins", "used_volume", "waste_volume", "total_waste_volume")
  let rawStocks ← problem.getObjValAs? (List Json) stockKey
  let rawRows ← solution.getObjValAs? (List Json) "layouts"
  unless rawStocks.length == certificate.stock.length && rawRows.length == certificate.layouts.length do
    throw "accounting rows differ from the packing certificate"
  let stocks ← (certificate.stock.zip rawStocks).mapM fun (stock, raw) => do
    let cost ← readNumericCost (← readDefault raw "cost" (Json.num ⟨1, 0⟩))
    return PricedMaterial.mk stock cost
  let rows ← (certificate.layouts.zip rawRows).mapM fun (layout, raw) => do
    return AccountingRow.mk layout (← raw.getObjValAs? Nat usedKey) (← raw.getObjValAs? Nat wasteKey)
      (← readNumericCost (← raw.getObjVal? "cost"))
  return ⟨stocks, certificate.demands, rows, certificate.shortages, certificate.layoutCount,
    ← solution.getObjValAs? Nat totalKey, ← readNumericCost (← solution.getObjVal? "total_cost")⟩

def checkAccounting1D (problem solution : Json) : Except String Bool := do
  return checkAccounting .linear (← readAccounting .linear problem solution)

def checkAccounting2D (problem solution : Json) : Except String Bool := do
  return checkAccounting .sheet (← readAccounting .sheet problem solution)

def checkAccounting3D (problem solution : Json) : Except String Bool := do
  return checkAccounting .box (← readAccounting .box problem solution)

private theorem accounting_output_sound (dim : Dimension) (problem solution : Json)
    (checked : (do return checkAccounting dim (← readAccounting dim problem solution)) = .ok true) :
    ∃ report, readAccounting dim problem solution = .ok report ∧ AccountingSound dim report := by
  cases decoded : readAccounting dim problem solution with
  | error => simp [decoded, bind, Except.bind] at checked
  | ok report =>
    have accepted : checkAccounting dim report = true := by
      simpa [decoded, bind, Except.bind, pure, Except.pure] using checked
    exact ⟨report, rfl, accounting_sound dim accepted⟩

theorem checkAccounting1D_sound {problem solution : Json}
    (checked : checkAccounting1D problem solution = .ok true) :
    ∃ report, readAccounting .linear problem solution = .ok report ∧ AccountingSound .linear report :=
  accounting_output_sound .linear problem solution checked

theorem checkAccounting2D_sound {problem solution : Json}
    (checked : checkAccounting2D problem solution = .ok true) :
    ∃ report, readAccounting .sheet problem solution = .ok report ∧ AccountingSound .sheet report :=
  accounting_output_sound .sheet problem solution checked

theorem checkAccounting3D_sound {problem solution : Json}
    (checked : checkAccounting3D problem solution = .ok true) :
    ∃ report, readAccounting .box problem solution = .ok report ∧ AccountingSound .box report :=
  accounting_output_sound .box problem solution checked

private inductive SawEffect (source : Saw.Source) (state next : Saw.State)
    (op : Saw.Operation) : Type where
  | unchanged (notCut : op.action.getObjValAs? String "kind" ≠ .ok "cut")
      (live : next.live.map Prod.fst = state.live.map Prod.fst)
      (history : next.history = state.history)
  | cut (cut : Saw.Cut) (sheet : Saw.SourceSheet) (turns : Nat)
      (kind : op.action.getObjValAs? String "kind" = .ok "cut")
      (decoded : fromJson? op.action = .ok cut)
      (sourceSheet : source.sheets[op.workpiece.sheet_index]? = some sheet)
      (splitOk : Saw.checkSplit sheet op.workpiece cut = true)
      (clears : Saw.bladeClears sheet.parts op.workpiece.bounds cut = true)
      (fresh : cut.children.all (fun child => !state.history.any (fun t => t.id == child)) = true)
      (parent : (op.workpiece, turns) ∈ state.live)
      (live : next.live = (state.live.filter (fun pair => pair.1 != op.workpiece)) ++
        cut.children.map (·, turns))
      (history : ∃ index, next.history = state.history ++
        cut.children.map (fun child => ⟨child, some op.workpiece, some index⟩))

private theorem rotate_live_ids (live : List (Saw.WorkpieceId × Nat)) (id : Saw.WorkpieceId)
    (requested : Nat) :
    (live.map (fun pair => if pair.1 == id then (id, requested) else pair)).map Prod.fst =
      live.map Prod.fst := by
  induction live with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, ih]
    by_cases h : head.1 = id <;> simp [h]

private theorem saw_step_effect {source : Saw.Source} {state next : Saw.State} {i : Nat}
    {op : Saw.Operation} (applied : state.apply source i op = .ok (some next)) :
    Nonempty (SawEffect source state next op) := by
  simp only [Saw.State.apply, bind, Except.bind, pure, Except.pure, throw] at applied
  cases hlive : state.live.find? (fun (piece, _) => piece == op.workpiece) with
  | none => simp [hlive] at applied
  | some pair =>
    rcases pair with ⟨id, turns⟩
    simp only [hlive] at applied
    cases htrace : state.history.find? (fun trace => trace.id == op.workpiece) with
    | none => simp [htrace] at applied
    | some trace =>
      simp only [htrace] at applied
      cases hsheet : source.sheets[op.workpiece.sheet_index]? with
      | none => simp [hsheet] at applied
      | some sheet =>
        simp only [hsheet] at applied
        split at applied
        · cases hkind : op.action.getObjValAs? String "kind" with
          | error err => simp [hkind] at applied
          | ok kind =>
            simp only [hkind] at applied
            split at applied
            · rename_i isHandle
              split at applied
              · cases applied
              · cases applied
                exact ⟨.unchanged (by simpa [hkind] using (show kind ≠ "cut" from by
                  intro eq; simp [eq] at isHandle)) rfl rfl⟩
            · split at applied
              · split at applied
                · cases hturn : op.action.getObjValAs? Nat "quarter_turns" <;>
                    simp only [hturn] at applied
                  · cases applied
                  · split at applied
                    · cases applied
                      exact ⟨.unchanged (by simp [hkind]) (rotate_live_ids _ _ _) rfl⟩
                    · cases applied
                · cases hsetup : op.action.getObjValAs? Saw.Setup "setup" <;>
                    simp only [hsetup] at applied
                  · cases applied
                  · cases hinitial : op.action.getObjValAs? Bool "initial" <;>
                      simp only [hinitial] at applied
                    · cases applied
                    · split at applied
                      · cases applied
                        exact ⟨.unchanged (by simp [hkind]) rfl rfl⟩
                      · cases applied
                · cases hcut : fromJson? (α := Saw.Cut) op.action <;> simp only [hcut] at applied
                  · cases applied
                  · rename_i cut
                    split at applied
                    · rename_i permitted
                      have actual : id = op.workpiece := by
                        simpa using List.find?_some hlive
                      subst id
                      simp only [Bool.and_eq_true] at permitted
                      cases applied
                      exact ⟨.cut cut sheet turns hkind hcut hsheet permitted.1.1.2 permitted.1.2
                        permitted.2 (List.mem_of_find?_eq_some hlive) rfl ⟨i, rfl⟩⟩
                    · cases applied
                · cases applied
              · cases applied
        · cases applied

/-- Sum the areas of live workpieces in sheet coordinates, regardless of machine rotation. -/
def sawLiveArea (state : Saw.State) : Nat :=
  (state.live.map (fun pair => pair.1.bounds.area)).sum

/-- Kerf charged by a successful step, including clipped edge passes. -/
def sawKerf (op : Saw.Operation) : Nat :=
  if (op.action.getObjValAs? String "kind").toOption == some "cut" then
    match fromJson? (α := Saw.Cut) op.action with
    | .ok cut => cut.kerf_region.area
    | .error _ => 0
  else 0

def SawLiveValid (state : Saw.State) : Prop :=
  (state.live.map Prod.fst).Nodup ∧ state.live.map Prod.fst ⊆ state.history.map Saw.Trace.id

private theorem sum_without {α β : Type} [DecidableEq α] (measure : α → Nat)
    (pairs : List (α × β)) (unique : (pairs.map Prod.fst).Nodup)
    {id : α} {value : β} (member : (id, value) ∈ pairs) :
    ((pairs.filter (fun pair => pair.1 != id)).map (fun pair => measure pair.1)).sum + measure id =
      (pairs.map (fun pair => measure pair.1)).sum := by
  induction pairs with
  | nil => simp at member
  | cons head tail ih =>
    have ⟨different, tailUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | member
    · subst head
      have keep : tail.filter (fun pair => pair.1 != id) = tail := by
        apply List.filter_eq_self.mpr
        intro pair hp
        have ne : pair.1 ≠ id := by
          intro h
          apply different
          have mapped : pair.1 ∈ tail.map Prod.fst := List.mem_map.mpr ⟨pair, hp, rfl⟩
          simpa only [h] using mapped
        simp [ne]
      simp [keep, Nat.add_comm]
    · have ne : head.1 ≠ id := by
        intro h
        apply different
        rw [h]
        exact List.mem_map_of_mem (f := Prod.fst) member
      have rest := ih tailUnique member
      simp only [List.filter_cons, bne_iff_ne, ite_eq_left ne, List.map_cons, List.sum_cons]
      omega

private theorem saw_children_unique {sheet : Saw.SourceSheet} {id : Saw.WorkpieceId} {cut : Saw.Cut}
    (accepted : Saw.checkSplit sheet id cut = true) : cut.children.Nodup := by
  simp only [Saw.checkSplit, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at accepted
  let start := Saw.lowCoordinate cut.kerf_region cut.axis
  let low := Saw.lowCoordinate id.bounds cut.axis
  let offset := start - low
  let removed := cut.kerf_region.extent cut.axis
  have bounds := accepted.1.1.1.1.1.1.1.1
  have progress : 0 < offset + removed := by
    change low ≤ start ∧ _ ∧ _ ∧ low < start + removed ∧ _ at bounds
    dsimp [offset]
    omega
  have different : id.bounds.low cut.axis offset ≠ id.bounds.high cut.axis (offset + removed) := by
    intro eq
    have same := congrArg (fun r => Saw.lowCoordinate r cut.axis) eq
    cases h : cut.axis <;>
      simp only [h, Saw.lowCoordinate, Staged.Region.low, Staged.Region.high] at same <;> omega
  rw [accepted.2]
  have unique : ([id.bounds.low cut.axis offset, id.bounds.high cut.axis (offset + removed)].map
      (fun region => Saw.WorkpieceId.mk id.sheet_index region)).Nodup := by
    simp [different]
  change ((([id.bounds.low cut.axis offset, id.bounds.high cut.axis (offset + removed)].filter
    _).map _)).Nodup
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp unique)).filter _

/-- A valid step preserves unique live workpieces and conserves area after charging its kerf. -/
theorem saw_apply_conserves_area {source : Saw.Source} {state next : Saw.State} {i : Nat}
    {op : Saw.Operation} (valid : SawLiveValid state) (applied : state.apply source i op = .ok (some next)) :
    SawLiveValid next ∧ sawLiveArea next + sawKerf op = sawLiveArea state := by
  obtain ⟨effect⟩ := saw_step_effect applied
  cases effect with
  | unchanged notCut live history =>
    have kerf : sawKerf op = 0 := by
      cases h : op.action.getObjValAs? String "kind" with
      | error => simp [sawKerf, h, Except.toOption]
      | ok kind =>
        have different : kind ≠ "cut" := by
          intro eq
          exact notCut (eq ▸ h)
        simp [sawKerf, h, Except.toOption, different]
    refine ⟨by simpa [SawLiveValid, live, history] using valid, ?_⟩
    simp only [kerf, Nat.add_zero, sawLiveArea]
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun ids => (ids.map (fun id : Saw.WorkpieceId => id.bounds.area)).sum) live
  | cut cut sheet turns kind decoded _ splitOk _ fresh parent live history =>
    have kerf : sawKerf op = cut.kerf_region.area := by simp [sawKerf, kind, decoded, Except.toOption]
    have children := saw_children_unique splitOk
    have splitArea := Saw.checkSplit_conserves_area splitOk
    have parentArea := sum_without (fun id : Saw.WorkpieceId => id.bounds.area) state.live valid.1 parent
    have filtered : ((state.live.filter (fun pair => pair.1 != op.workpiece)).map Prod.fst) ⊆
        state.live.map Prod.fst := by
      intro id hm
      obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (List.mem_filter.mp hp).1
    have disjoint : ∀ x ∈ (state.live.filter (fun pair => pair.1 != op.workpiece)).map Prod.fst,
        ∀ y ∈ cut.children, x ≠ y := by
      intro x hx y hy eq
      subst y
      have old := valid.2 (filtered hx)
      obtain ⟨trace, ht, rfl⟩ := List.mem_map.mp old
      have rejected := (List.all_eq_true.mp fresh) trace.id hy
      have accepted : state.history.any (fun prev => prev.id == trace.id) = true :=
        List.any_eq_true.mpr ⟨trace, ht, by simp⟩
      simp [accepted] at rejected
    have liveIds : next.live.map Prod.fst =
        (state.live.filter (fun pair => pair.1 != op.workpiece)).map Prod.fst ++ cut.children := by
      rw [live, List.map_append, List.map_map]
      simp [Function.comp_def]
    obtain ⟨index, history⟩ := history
    have historyIds : next.history.map Saw.Trace.id =
        state.history.map Saw.Trace.id ++ cut.children := by
      rw [history, List.map_append, List.map_map]
      simp [Function.comp_def]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [liveIds, List.nodup_iff_pairwise_ne, List.pairwise_append]
      refine ⟨List.pairwise_map.mpr ((List.pairwise_map.mp valid.1).filter _), children, disjoint⟩
    · intro id hm
      rw [liveIds] at hm
      rw [historyIds]
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ (valid.2 (filtered hm))
      · exact List.mem_append_right _ hm
    · simp only [sawLiveArea, live, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, kerf]
      omega

/-- A cut accepted by the saw state machine cannot cross any intact part contained
in the parent workpiece, including at a zero-width blade line. -/
theorem saw_cut_preserves_parts {source : Saw.Source} {state next : Saw.State} {i : Nat}
    {op : Saw.Operation} {cut : Saw.Cut} {sheet : Saw.SourceSheet}
    (applied : state.apply source i op = .ok (some next))
    (kind : op.action.getObjValAs? String "kind" = .ok "cut")
    (decoded : fromJson? op.action = .ok cut)
    (sourceSheet : source.sheets[op.workpiece.sheet_index]? = some sheet)
    {part : Staged.Region} (finished : part ∈ sheet.parts)
    (inside : Saw.includes op.workpiece.bounds part = true) :
    ¬part.crossesBlade op.workpiece.bounds cut.axis
      (Saw.lowCoordinate cut.kerf_region cut.axis - Saw.lowCoordinate op.workpiece.bounds cut.axis)
      (cut.kerf_region.extent cut.axis) := by
  obtain ⟨effect⟩ := saw_step_effect applied
  cases effect with
  | unchanged notCut _ _ => exact False.elim (notCut kind)
  | cut actual actualSheet _ _ hcut hsheet splitOk clears _ _ _ _ =>
    rw [decoded] at hcut
    rw [sourceSheet] at hsheet
    cases hcut
    cases hsheet
    have clear := List.all_eq_true.mp clears part finished
    simp only [inside, Bool.not_true, Bool.false_or, decide_eq_true_eq] at clear
    simp only [Saw.checkSplit, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at splitOk
    have start := splitOk.1.1.1.1.1.1.1.1.1
    cases h : cut.axis <;>
      simp only [h, Saw.lowCoordinate, Staged.Region.extent, Staged.Region.crossesBlade]
        at start clear ⊢ <;> omega

def sawRoots (source : Saw.Source) : List Saw.WorkpieceId :=
  source.sheets.zipIdx.map (fun (sheet, index) => ⟨index, sheet.root⟩)

def sawInitial (source : Saw.Source) : Saw.State :=
  { history := (sawRoots source).map (fun id => ⟨id, none, none⟩)
    live := (sawRoots source).map (·, 0) }

def sawRootArea (source : Saw.Source) : Nat :=
  (source.sheets.map (fun sheet => sheet.root.area)).sum

/-- Successful indexed replay, with the total area removed by the blade. -/
inductive SawSchedule (source : Saw.Source) :
    Nat → Saw.State → List Saw.Operation → Saw.State → Nat → Prop where
  | nil (index state) : SawSchedule source index state [] state 0
  | cons {index state next final kerf op rest}
      (step : state.apply source index op = .ok (some next))
      (tail : SawSchedule source (index + 1) next rest final kerf) :
      SawSchedule source index state (op :: rest) final (sawKerf op + kerf)

private theorem saw_initial_valid (source : Saw.Source) : SawLiveValid (sawInitial source) := by
  simp only [SawLiveValid, sawInitial, List.map_map, Function.comp_def,
    List.Subset.refl, and_true]
  rw [sawRoots, List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj ordered same
  have eq := congrArg Saw.WorkpieceId.sheet_index same
  simp [List.getElem_zipIdx] at eq
  omega

private theorem saw_replay_conserves_area {source : Saw.Source} {index : Nat}
    {state final : Saw.State} {operations : List Saw.Operation} {kerf : Nat}
    (replay : SawSchedule source index state operations final kerf) (valid : SawLiveValid state) :
    SawLiveValid final ∧ sawLiveArea final + kerf = sawLiveArea state := by
  induction replay with
  | nil => exact ⟨valid, Nat.add_zero _⟩
  | cons step _ ih =>
    have ⟨nextValid, stepArea⟩ := saw_apply_conserves_area valid step
    have ⟨finalValid, restArea⟩ := ih nextValid
    exact ⟨finalValid, by omega⟩

/-- A full successful replay accounts exactly for the original root sheets. -/
theorem saw_schedule_conserves_area {source : Saw.Source} {final : Saw.State}
    {operations : List Saw.Operation} {kerf : Nat}
    (replay : SawSchedule source 0 (sawInitial source) operations final kerf) :
    SawLiveValid final ∧ sawLiveArea final + kerf = sawRootArea source := by
  have initialArea : sawLiveArea (sawInitial source) = sawRootArea source := by
    simp only [sawLiveArea, sawInitial, sawRoots, sawRootArea, List.map_map, Function.comp_def]
    change ((source.sheets.zipIdx).map ((fun sheet : Saw.SourceSheet => sheet.root.area) ∘ Prod.fst)).sum = _
    rw [← List.map_map]
    simp
  rw [← initialArea]
  exact saw_replay_conserves_area replay (saw_initial_valid source)


-- Audit all theorems in this namespace, including private proof helpers.
run_cmd do
  let standard := [`propext, `Quot.sound, `Classical.choice]
  let declarations := (← getEnv).constants.foldStage2 (fun names name info =>
    if info.isTheorem && (`Packing.Semantics).isPrefixOf (privateToUserName name) then
      names.push name
    else names) #[]
  for theoremName in declarations do
    for assumption in ← Lean.collectAxioms theoremName do
      unless standard.contains assumption do
        throwError "unexpected axiom {assumption} in {theoremName}"

end Packing.Semantics
