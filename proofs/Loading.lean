import Indexed

set_option warningAsError true

namespace Packing.Loading

open Lean

inductive FloorAxis where
  | x | z
  deriving FromJson

inductive Delivery where
  | none | only_x_movements | only_z_movements | increasing_x | increasing_z
  deriving DecidableEq, FromJson

structure ItemRule where
  stackability_id : Nat := 0
  nesting_height : Nat := 0
  maximum_stackability : Option Nat := none
  maximum_weight_above : Option Nat := none
  group_id : Nat := 0

instance : FromJson ItemRule where
  fromJson? j := do
    return ⟨← readDefault j "stackability_id" 0, ← readDefault j "nesting_height" 0,
      ← readDefault j "maximum_stackability" none, ← readDefault j "maximum_weight_above" none,
      ← readDefault j "group_id" 0⟩

structure Density where
  numerator : Nat
  denominator : Nat
  deriving FromJson

structure Axles where
  axis : FloorAxis
  front_position : Nat
  rear_position : Nat
  front_maximum : Nat
  rear_maximum : Nat
  front_tare : Nat := 0
  rear_tare : Nat := 0

instance : FromJson Axles where
  fromJson? j := do
    return ⟨← j.getObjValAs? FloorAxis "axis", ← j.getObjValAs? Nat "front_position",
      ← j.getObjValAs? Nat "rear_position", ← j.getObjValAs? Nat "front_maximum",
      ← j.getObjValAs? Nat "rear_maximum", ← readDefault j "front_tare" 0,
      ← readDefault j "rear_tare" 0⟩

structure AxleReactions where
  front : Nat
  rear : Nat
  deriving FromJson

structure FloorRect where
  x : Nat
  z : Nat
  width : Nat
  depth : Nat
  deriving FromJson

structure BinRule where
  maximum_stack_density : Option Density := none
  axle_limits : Option Axles := none
  defects : List FloorRect := []

instance : FromJson BinRule where
  fromJson? j := do
    return ⟨← readDefault j "maximum_stack_density" none, ← readDefault j "axle_limits" none,
      ← readDefault j "defects" []⟩

structure ItemPlacement where
  demand_index : Nat
  y : Nat
  rotation : String
  deriving FromJson

structure Column where
  x : Nat
  z : Nat
  width : Nat
  depth : Nat
  height : Nat
  weight : Nat
  items : List ItemPlacement
  deriving FromJson

structure BinLayout where
  bin_index : Nat
  payload : Nat
  stacks : List Column
  axle_loads : Option AxleReactions
  deriving FromJson

structure Shortage where
  demand_index : Nat
  quantity : Nat
  deriving DecidableEq, FromJson

structure NestedItem where
  y : Nat
  height : Nat
  recess : Nat

def Nested (finalTop : Nat) (base : Nat) : List NestedItem → Prop
  | [] => base = finalTop
  | item :: rest =>
    item.recess < item.height ∧ item.y + item.recess = base ∧
      Nested finalTop (item.y + item.height) rest

def checkNesting (finalTop : Nat) (base : Nat) : List NestedItem → Bool
  | [] => decide (base = finalTop)
  | item :: rest =>
    decide (item.recess < item.height ∧ item.y + item.recess = base) &&
      checkNesting finalTop (item.y + item.height) rest

theorem checkNesting_iff (items : List NestedItem) (base finalTop : Nat) :
    checkNesting finalTop base items = true ↔ Nested finalTop base items := by
  induction items generalizing base <;> simp_all [checkNesting, Nested, Bool.and_eq_true, and_assoc]

theorem nested_top_monotone (items : List NestedItem) (base finalTop : Nat)
    (h : Nested finalTop base items) : base ≤ finalTop := by
  induction items generalizing base with
  | nil => simpa [Nested] using Nat.le_of_eq h
  | cons item rest ih =>
    obtain ⟨hrecess, hbase, hrest⟩ := h
    have htop := ih _ hrest
    omega

/-- Checking the final top bounds the full physical height of every nested item. -/
theorem nested_items_under_top (items : List NestedItem) (base finalTop : Nat)
    (h : Nested finalTop base items) : ∀ item ∈ items, item.y + item.height ≤ finalTop := by
  induction items generalizing base with
  | nil => simp
  | cons item rest ih =>
    intro current hm
    have hrest := h.2.2
    rcases List.mem_cons.mp hm with rfl | hm
    · exact nested_top_monotone rest _ _ hrest
    · exact ih _ hrest current hm

def Axles.scale (axles : Axles) : Int :=
  2 * (axles.rear_position : Int) - 2 * (axles.front_position : Int)

def Axles.frontReaction (axles : Axles) (mass moment : Int) : Int :=
  2 * (axles.rear_position : Int) * mass - moment + axles.front_tare * axles.scale

def Axles.rearReaction (axles : Axles) (mass moment : Int) : Int :=
  moment - 2 * (axles.front_position : Int) * mass + axles.rear_tare * axles.scale

/-- Twice-moment arithmetic conserves the total cargo weight and both tares exactly. -/
theorem axle_conserves_weight (axles : Axles) (mass moment : Int) :
    axles.frontReaction mass moment + axles.rearReaction mass moment =
      axles.scale * (mass + axles.front_tare + axles.rear_tare) := by
  unfold Axles.frontReaction Axles.rearReaction
  rw [Int.mul_add, Int.mul_add, Int.mul_comm axles.scale (axles.front_tare : Int),
    Int.mul_comm axles.scale (axles.rear_tare : Int)]
  simp only [Axles.scale, Int.sub_mul]
  omega

def ExactReaction (scale reaction : Int) (maximum reported : Nat) : Prop :=
  0 < scale ∧ 0 ≤ reaction ∧ reaction ≤ maximum * scale ∧
    ((reported : Int) - 1) * scale < reaction ∧ reaction ≤ reported * scale

instance (scale reaction : Int) (maximum reported : Nat) :
    Decidable (ExactReaction scale reaction maximum reported) := by
  unfold ExactReaction
  infer_instance

theorem reaction_ceiling_within_cap {scale reaction : Int} {maximum reported : Nat}
    (h : ExactReaction scale reaction maximum reported) : reported ≤ maximum := by
  obtain ⟨hscale, _, hlimit, hround, _⟩ := h
  apply Classical.byContradiction
  intro hcap
  have hcast : (maximum : Int) ≤ (reported : Int) - 1 := by omega
  have hmon := Int.mul_le_mul_of_nonneg_right hcast (Int.le_of_lt hscale)
  omega

def Axles.reactionsFit (axles : Axles) (mass moment : Int) : Bool :=
  decide (0 < axles.scale ∧
    0 ≤ axles.frontReaction mass moment ∧
    axles.frontReaction mass moment ≤ axles.front_maximum * axles.scale ∧
    0 ≤ axles.rearReaction mass moment ∧
    axles.rearReaction mass moment ≤ axles.rear_maximum * axles.scale)

def Axles.checkReported (axles : Axles) (mass moment : Int) (reported : AxleReactions) : Bool :=
  decide (ExactReaction axles.scale (axles.frontReaction mass moment)
    axles.front_maximum reported.front ∧
    ExactReaction axles.scale (axles.rearReaction mass moment)
      axles.rear_maximum reported.rear)

def FloorRect.piece (rect : FloorRect) (height : Nat) : Piece :=
  ⟨"", ⟨rect.x, 0, rect.z⟩, ⟨rect.width, height, rect.depth⟩, ""⟩

def Column.floor (column : Column) : FloorRect :=
  ⟨column.x, column.z, column.width, column.depth⟩

structure Cargo where
  footprint : FloorRect
  mass : Nat
  groupId : Nat

def Axles.cargoForSupports (axles : Axles) (cargo : List Cargo) : Int × Int :=
  let moment : Nat := (cargo.map (fun item =>
    let twiceCenter := match axles.axis with
      | .x => 2 * item.footprint.x + item.footprint.width
      | .z => 2 * item.footprint.z + item.footprint.depth
    item.mass * twiceCenter)).sum
  ((cargo.map Cargo.mass).sum, moment)

def checkAxles (delivery : Delivery) (stock : Stock) (cargo : List Cargo)
    (limits : Option Axles) (reported : Option AxleReactions) : Bool :=
  match limits, reported with
  | none, none => true
  | some axles, some report =>
    let extent := match axles.axis with | .x => stock.extent.x | .z => stock.extent.z
    let (mass, moment) := axles.cargoForSupports cargo
    decide (axles.front_position < axles.rear_position ∧ axles.rear_position ≤ extent) &&
      axles.reactionsFit 0 0 && axles.checkReported mass moment report &&
      (delivery == .none || (cargo.map Cargo.groupId).all fun groupId =>
        let (mass, moment) := axles.cargoForSupports (cargo.filter (fun c => groupId ≤ c.groupId))
        axles.reactionsFit mass moment)
  | _, _ => false

def deliveryPair (rule : Delivery) (a b : Cargo) : Bool :=
  if a.groupId == b.groupId then true else
  let (early, late) :=
    if a.groupId < b.groupId then (a.footprint, b.footprint) else (b.footprint, a.footprint)
  match rule with
  | .none => true
  | .increasing_x => decide (late.x ≤ early.x)
  | .increasing_z => decide (late.z ≤ early.z)
  | .only_x_movements => decide
    (late.z + late.depth ≤ early.z ∨ early.z + early.depth ≤ late.z ∨
      late.x + late.width ≤ early.x)
  | .only_z_movements => decide
    (late.x + late.width ≤ early.x ∨ early.x + early.width ≤ late.x ∨
      late.z + late.depth ≤ early.z)

def pairsAcrossColumns (rule : Delivery) : List (List Cargo) → Bool
  | [] => true
  | column :: rest =>
    column.all (fun item => rest.all (fun other => other.all (deliveryPair rule item))) &&
      pairsAcrossColumns rule rest

def checkWeightsAbove : List (Option Nat × Nat) → Nat → Bool
  | [], _ => true
  | (limit, weight) :: rest, above =>
    Indexed.limitFits limit above && checkWeightsAbove rest (above + weight)

def readColumn (delivery : Delivery) (column : Column) (rules : List ItemRule)
    (demands : List Demand) (weights : List Nat) : Except String (Bool × List Cargo) := do
  if column.items.isEmpty then return (false, [])
  let mut nested : List NestedItem := []
  let mut cargo : List Cargo := []
  let mut weightsAbove : List (Option Nat × Nat) := []
  let mut stackClass : Option Nat := none
  let mut lowerGroup : Option Nat := none
  for item in column.items do
    let some demand := demands[item.demand_index]? | throw "unknown stack item source"
    let rule := rules[item.demand_index]?.getD {}
    let mass := weights[item.demand_index]?.getD 0
    let some (_, extent) := demand.orientations.find? (fun (rotation, _) => rotation == item.rotation)
      | return (false, [])
    unless (item.rotation == "xyz" || item.rotation == "zyx") &&
        extent.x == column.width && extent.z == column.depth &&
        rule.nesting_height < extent.y &&
        (stackClass.isNone || stackClass == some rule.stackability_id) &&
        Indexed.limitFits rule.maximum_stackability column.items.length &&
        (delivery == .none || Indexed.limitFits lowerGroup rule.group_id) do
      return (false, [])
    let recess := if nested.isEmpty then 0 else rule.nesting_height
    nested := ⟨item.y, extent.y, recess⟩ :: nested
    cargo := ⟨column.floor, mass, rule.group_id⟩ :: cargo
    weightsAbove := (rule.maximum_weight_above, mass) :: weightsAbove
    stackClass := some rule.stackability_id
    lowerGroup := some rule.group_id
  return (checkNesting column.height 0 nested.reverse &&
    Indexed.checkPayload none column.weight (cargo.map Cargo.mass) &&
    checkWeightsAbove weightsAbove 0, cargo)

def checkLayout (delivery : Delivery) (layout : BinLayout) (stock : Stock) (binRule : BinRule)
    (rules : List ItemRule) (demands : List Demand) (weights : List Nat) (limit : Option Nat) :
    Except String Bool := do
  let columns := layout.stacks.map (fun column => column.floor.piece column.height)
  let footprintLayout : Layout := ⟨stock.name, stock.extent, columns, none⟩
  unless !columns.isEmpty && footprintLayout.check stock &&
      columns.all (fun column => binRule.defects.all
        (fun defect => decide (Separated 0 column (defect.piece stock.extent.y)))) do
    return false
  let checked ← layout.stacks.mapM fun column => readColumn delivery column rules demands weights
  unless (layout.stacks.zip checked).all (fun (column, ok, _) =>
      ok && binRule.maximum_stack_density.elim true (fun density =>
        decide (0 < density.denominator ∧
          column.weight * density.denominator ≤ density.numerator * column.width * column.depth))) do
    return false
  let cargo := checked.map Prod.snd
  return Indexed.checkPayload limit layout.payload (cargo.flatten.map Cargo.mass) &&
    pairsAcrossColumns delivery cargo &&
    checkAxles delivery stock cargo.flatten binRule.axle_limits layout.axle_loads

def checkLoading (problem output : Json) : Except String Bool := do
  let packing ← problem.getObjVal? "packing"
  let source ← packing.getObjVal? "problem"
  let stocks ← (← source.getObjValAs? (List Json) "bins").mapM (readStock .box)
  let demands ← (← source.getObjValAs? (List Json) "demands").mapM (readDemand .box)
  let weights ← readDefault packing "item_weights" ([] : List Nat)
  let limits ← readDefault packing "bin_max_weights" ([] : List (Option Nat))
  let itemRules ← readDefault problem "item_rules" ([] : List ItemRule)
  let binRules ← readDefault problem "bin_rules" ([] : List BinRule)
  let delivery ← readDefault problem "unloading" Delivery.none
  let layouts ← output.getObjValAs? (List BinLayout) "layouts"
  let unplaced ← output.getObjValAs? (List Shortage) "unplaced"
  let layoutCount ← output.getObjValAs? Nat "bin_count"
  unless (weights.isEmpty || weights.length == demands.length) &&
      (itemRules.isEmpty || itemRules.length == demands.length) &&
      (limits.isEmpty || limits.length == stocks.length) &&
      (binRules.isEmpty || binRules.length == stocks.length) &&
      layoutCount == layouts.length do
    return false
  for layout in layouts do
    let some stock := stocks[layout.bin_index]? | throw "unknown loaded bin source"
    unless ← checkLayout delivery layout stock (binRules[layout.bin_index]?.getD {})
        itemRules demands weights limits[layout.bin_index]?.join do
      return false
  let used := layouts.map BinLayout.bin_index
  let placed := layouts.flatMap (fun bin =>
    bin.stacks.flatMap (fun column => column.items.map ItemPlacement.demand_index))
  let shortages := demands.zipIdx.filterMap fun (demand, index) =>
    let missing := demand.quantity - placed.count index
    if missing == 0 then none else some { demand_index := index, quantity := missing }
  return unplaced == shortages &&
    demands.zipIdx.all (fun (demand, index) => decide (placed.count index ≤ demand.quantity)) &&
    stocks.zipIdx.all (fun (stock, index) => Indexed.limitFits stock.limit (used.count index))

end Packing.Loading
