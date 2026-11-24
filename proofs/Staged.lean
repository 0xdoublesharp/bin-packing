import Indexed

set_option warningAsError true

namespace Packing.Staged

open Lean

inductive Axis where
  | vertical | horizontal
  deriving DecidableEq, FromJson

structure Region where
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  deriving DecidableEq, FromJson, Repr

def Region.area (r : Region) : Nat := r.width * r.height

def Region.extent (r : Region) (axis : Axis) : Nat :=
  match axis with
  | .vertical => r.width
  | .horizontal => r.height

def Region.crossExtent (r : Region) (axis : Axis) : Nat :=
  match axis with
  | .vertical => r.height
  | .horizontal => r.width

def Region.low (r : Region) (axis : Axis) (offset : Nat) : Region :=
  match axis with
  | .vertical => { r with width := offset }
  | .horizontal => { r with height := offset }

def Region.high (r : Region) (axis : Axis) (endOffset : Nat) : Region :=
  match axis with
  | .vertical => { r with x := r.x + endOffset, width := r.width - endOffset }
  | .horizontal => { r with y := r.y + endOffset, height := r.height - endOffset }

def Region.bladeArea (r : Region) (axis : Axis) (kerf : Nat) : Nat :=
  kerf * r.crossExtent axis

private theorem cut_lengths (length offset kerf : Nat) (h : offset + kerf ≤ length) :
    offset + (length - (offset + kerf)) + kerf = length := by omega

theorem cut_area (r : Region) (axis : Axis) (offset kerf : Nat)
    (h : offset + kerf ≤ r.extent axis) :
    (r.low axis offset).area + (r.high axis (offset + kerf)).area + r.bladeArea axis kerf =
      r.area := by
  cases axis <;> simp only [Region.low, Region.high, Region.bladeArea, Region.area,
    Region.crossExtent, Region.extent] at *
  · rw [← Nat.add_mul, ← Nat.add_mul, cut_lengths _ _ _ h]
  · rw [Nat.mul_comm r.width offset, Nat.mul_comm r.width (r.height - (offset + kerf)),
      ← Nat.add_mul, ← Nat.add_mul, cut_lengths _ _ _ h, Nat.mul_comm]

structure Part where
  node : Nat
  demand : Nat
  rotated : Bool
  region : Region
  deriving DecidableEq

inductive Tree where
  | empty
  | part (p : Part)
  | waste (r : Region)
  | cut (r : Region) (axis : Axis) (offset : Nat) (low high : Tree)

def Tree.check (kerf : Nat) (expected : Region) : Tree → Bool
  | .empty => decide (expected.area = 0)
  | .part p => decide (p.region = expected ∧ 0 < expected.area)
  | .waste r => decide (r = expected ∧ 0 < expected.area)
  | .cut r axis offset low high =>
    decide (r = expected ∧ 0 < r.area ∧ offset + kerf ≤ r.extent axis ∧
      (kerf > 0 ∨ (0 < offset ∧ offset < r.extent axis)) ∧ kerf < r.extent axis) &&
    low.check kerf (r.low axis offset) && high.check kerf (r.high axis (offset + kerf))

def Tree.leafArea : Tree → Nat
  | .empty => 0
  | .part p => p.region.area
  | .waste r => r.area
  | .cut _ _ _ low high => low.leafArea + high.leafArea

def Tree.kerfArea (kerf : Nat) : Tree → Nat
  | .empty | .part _ | .waste _ => 0
  | .cut r axis _ low high =>
    r.bladeArea axis kerf + (low.kerfArea kerf + high.kerfArea kerf)

/-- Validated descendants and blade losses account for all prepared material. -/
theorem Tree.conserves_area (tree : Tree) (kerf : Nat) (expected : Region)
    (h : tree.check kerf expected = true) :
    tree.leafArea + tree.kerfArea kerf = expected.area := by
  induction tree generalizing expected with
  | empty => simpa [Tree.check, Tree.leafArea, Tree.kerfArea, eq_comm] using h
  | part p =>
    simp [Tree.check] at h
    simp [Tree.leafArea, Tree.kerfArea, h.1]
  | waste r =>
    simp [Tree.check] at h
    simp [Tree.leafArea, Tree.kerfArea, h.1]
  | cut r axis offset low high ihLow ihHigh =>
    simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, _, hposition, _, _⟩, hlow⟩, hhigh⟩ := h
    have heqLow := ihLow _ hlow
    have heqHigh := ihHigh _ hhigh
    have hsplit := cut_area r axis offset kerf hposition
    simp only [Tree.leafArea, Tree.kerfArea]
    omega

def Tree.parts : Tree → List Part
  | .empty | .waste _ => []
  | .part p => [p]
  | .cut _ _ _ low high => low.parts ++ high.parts

def Region.ofPiece (piece : Piece) : Region :=
  ⟨piece.origin.x, piece.origin.y, piece.extent.x, piece.extent.y⟩

def Region.crossesBlade (defect r : Region) (axis : Axis) (offset kerf : Nat) : Prop :=
  match axis with
  | .vertical =>
    r.y < defect.y + defect.height ∧ defect.y < r.y + r.height ∧
    defect.x < r.x + offset + kerf ∧ r.x + offset < defect.x + defect.width
  | .horizontal =>
    r.x < defect.x + defect.width ∧ defect.x < r.x + r.width ∧
    defect.y < r.y + offset + kerf ∧ r.y + offset < defect.y + defect.height

instance (d r : Region) (axis : Axis) (offset kerf : Nat) :
    Decidable (Region.crossesBlade d r axis offset kerf) := by
  cases axis <;> unfold Region.crossesBlade <;> infer_instance

def Tree.avoidsBlades (kerf : Nat) (defect : Region) : Tree → Bool
  | .empty | .part _ | .waste _ => true
  | .cut r axis offset low high =>
    decide (¬ defect.crossesBlade r axis offset kerf) &&
    low.avoidsBlades kerf defect && high.avoidsBlades kerf defect

def Tree.BladeClear (kerf : Nat) (defect : Region) : Tree → Prop
  | .empty | .part _ | .waste _ => True
  | .cut r axis offset low high =>
    ¬ defect.crossesBlade r axis offset kerf ∧
    low.BladeClear kerf defect ∧ high.BladeClear kerf defect

theorem Tree.avoidsBlades_iff (tree : Tree) (kerf : Nat) (defect : Region) :
    tree.avoidsBlades kerf defect = true ↔ tree.BladeClear kerf defect := by
  induction tree <;> simp_all [Tree.avoidsBlades, Tree.BladeClear, Bool.and_eq_true, and_assoc]

/-- Compare the indexed wire tree with the two permitted material children. -/
def decodeTree (nodes : Array Json) (kerf : Nat) (fuel index : Nat) :
    StateT (List Nat) (Except String) Tree :=
  match fuel with
  | 0 => throw "cut tree is cyclic or too deep"
  | fuel + 1 => do
    let seen ← get
    if seen.contains index then throw "cut tree reuses a node"
    set (index :: seen)
    let some node := nodes[index]? | throw s!"unknown cut-tree node {index}"
    let region ← node.getObjValAs? Region "region"
    let action ← node.getObjVal? "action"
    let kind ← action.getObjValAs? String "kind"
    match kind with
    | "part" =>
      return .part ⟨index, ← action.getObjValAs? Nat "demand_index",
        ← action.getObjValAs? Bool "rotated", region⟩
    | "waste" => return .waste region
    | "cut" =>
      let axis ← action.getObjValAs? Axis "axis"
      let offset ← action.getObjValAs? Nat "offset"
      let children ← action.getObjValAs? (List Nat) "children"
      let (lowIndex, highIndex) ←
        match (region.low axis offset).area != 0,
              (region.high axis (offset + kerf)).area != 0, children with
        | true, true, [lo, hi] => pure (some lo, some hi)
        | true, false, [lo] => pure (some lo, none)
        | false, true, [hi] => pure (none, some hi)
        | _, _, _ => throw "cut does not list its nonempty children in material order"
      let low ← lowIndex.elim (pure .empty) (decodeTree nodes kerf fuel)
      let high ← highIndex.elim (pure .empty) (decodeTree nodes kerf fuel)
      return .cut region axis offset low high
    | _ => throw s!"unknown cut-tree action {kind}"

inductive FirstAxis where
  | any | vertical | horizontal
  deriving FromJson

inductive CutType where
  | exact | non_exact | homogeneous | roadef2018
  deriving DecidableEq, FromJson

structure Rules where
  max_stages : Option Nat := some 3
  first_axis : FirstAxis := .vertical
  cut_type : CutType := .non_exact
  minimum_distance_1_cuts : Nat := 0
  maximum_distance_1_cuts : Option Nat := none
  minimum_distance_2_cuts : Nat := 0
  maximum_distance_2_cuts : Option Nat := none
  maximum_number_1_cuts : Option Nat := none
  maximum_number_2_cuts : Option Nat := none
  minimum_waste_length : Nat := 0
  cut_through_defects : Bool := false

instance : FromJson Rules where
  fromJson? j := do
    let defaults : Rules := {}
    return ⟨← readDefault j "max_stages" defaults.max_stages,
      ← readDefault j "first_axis" defaults.first_axis,
      ← readDefault j "cut_type" defaults.cut_type,
      ← readDefault j "minimum_distance_1_cuts" defaults.minimum_distance_1_cuts,
      ← readDefault j "maximum_distance_1_cuts" defaults.maximum_distance_1_cuts,
      ← readDefault j "minimum_distance_2_cuts" defaults.minimum_distance_2_cuts,
      ← readDefault j "maximum_distance_2_cuts" defaults.maximum_distance_2_cuts,
      ← readDefault j "maximum_number_1_cuts" defaults.maximum_number_1_cuts,
      ← readDefault j "maximum_number_2_cuts" defaults.maximum_number_2_cuts,
      ← readDefault j "minimum_waste_length" defaults.minimum_waste_length,
      ← readDefault j "cut_through_defects" defaults.cut_through_defects⟩

def FirstAxis.permits (rule : FirstAxis) (actual : Axis) : Bool :=
  match rule with
  | .any => true
  | .vertical => actual == .vertical
  | .horizontal => actual == .horizontal

def cutStage (first : Axis) (previous : Option Axis) (level : Nat) (current : Axis) : Nat :=
  match previous with
  | none => if first == current then 1 else 2
  | some axis => if axis == current then level else level + 1

def Tree.parallelCuts (axis : Axis) : Tree → Nat
  | .cut _ current _ low high =>
    if current == axis then 1 + low.parallelCuts axis + high.parallelCuts axis else 0
  | _ => 0

def Tree.wasteRegions : Tree → List Region
  | .empty | .part _ => []
  | .waste region => [region]
  | .cut _ _ _ low high => low.wasteRegions ++ high.wasteRegions

structure StageBlock where
  stage : Nat
  cutCount : Nat
  demands : List Nat
  wasteCount : Nat

def Tree.stageBlocks (first : Axis) (previous : Option Axis) (level : Nat) :
    Tree → List StageBlock
  | tree@(.cut _ axis _ low high) =>
    let stage := cutStage first previous level axis
    let descendants := low.stageBlocks first (some axis) stage ++
      high.stageBlocks first (some axis) stage
    if previous == some axis then descendants
    else ⟨stage, tree.parallelCuts axis, tree.parts.map Part.demand, tree.wasteRegions.length⟩ ::
      descendants
  | _ => []

def Tree.strips (first : Axis) (previous : Option Axis) (level : Nat) :
    Tree → List (Nat × Nat)
  | .empty | .waste _ => []
  | .part leaf =>
    match previous with
    | some axis => [(level, leaf.region.extent axis)]
    | none => []
  | tree@(.cut region axis _ low high) =>
    let stage := cutStage first previous level axis
    let descendants := low.strips first (some axis) stage ++ high.strips first (some axis) stage
    match previous with
    | some prior =>
      if prior != axis && !tree.parts.isEmpty then (level, region.extent prior) :: descendants
      else descendants
    | none => descendants

def checkDistance (rules : Rules) (strip : Nat × Nat) : Bool :=
  let (stage, extent) := strip
  match stage with
  | 1 => decide (rules.minimum_distance_1_cuts ≤ extent) &&
    Indexed.limitFits rules.maximum_distance_1_cuts extent
  | 2 => decide (rules.minimum_distance_2_cuts ≤ extent) &&
    Indexed.limitFits rules.maximum_distance_2_cuts extent
  | _ => true

def checkStages (rules : Rules) (first : Axis) (root : Region) (tree : Tree) : Bool :=
  let blocks := tree.stageBlocks first none 0
  let deepest := (blocks.map StageBlock.stage).foldl max 0
  let terminal := rules.max_stages.getD deepest
  let finishingMax := match rules.cut_type with
    | .non_exact => 1
    | .roadef2018 => 2
    | _ => 0
  let discounted := deepest != 0 && (blocks.filter (fun block => block.stage == deepest)).all
    (fun block => decide (0 < block.demands.length ∧ block.demands.length ≤ finishingMax ∧
      block.wasteCount ≤ 1))
  let limits := blocks.all fun block =>
    let cutCountOk := match block.stage with
      | 1 => Indexed.limitFits rules.maximum_number_1_cuts block.cutCount
      | 2 => Indexed.limitFits rules.maximum_number_2_cuts block.cutCount
      | _ => true
    cutCountOk && (if rules.cut_type == .homogeneous && block.stage == terminal
      then block.demands.all (fun d => block.demands.head? == some d) else true)
  let hasFirstStage := blocks.any (fun block => block.stage == 1)
  rules.first_axis.permits first && limits &&
    (hasFirstStage || checkDistance rules (1, root.extent first)) &&
    (tree.strips first none 0).all (checkDistance rules) &&
    tree.wasteRegions.all (fun r =>
      decide (rules.minimum_waste_length ≤ r.width ∧ rules.minimum_waste_length ≤ r.height)) &&
    Indexed.limitFits rules.max_stages (deepest - if discounted then 1 else 0)

def checkGroups (groups : List (Option Nat)) (demands : List Demand) : List Nat → List Nat → Bool
  | _, [] => true
  | produced, current :: rest =>
    let allowed := match groups[current]?.join with
      | none => true
      | some group => ((demands.zip groups).take current).zipIdx.all
        (fun ((demand, membership), index) =>
          membership != some group || produced.count index == demand.quantity)
    allowed && checkGroups groups demands (current :: produced) rest

structure ProductionPart where
  layout_index : Nat
  node_index : Nat
  deriving DecidableEq, FromJson

def checkStaged (problem output : Json) : Except String Bool := do
  let packing ← problem.getObjVal? "packing"
  let result ← Indexed.readIndexed .sheet (← packing.getObjVal? "problem") output
  let constraints ← Indexed.sheetRules packing result.stocks
  let rules ← readDefault problem "rules" ({} : Rules)
  let groups ← readDefault problem "groups" ([] : List (Option Nat))
  let trees ← output.getObjValAs? (List Json) "trees"
  let reportedUnplaced ← output.getObjValAs? (List Nat) "unplaced_quantities"
  let productionOrder ← output.getObjValAs? (List ProductionPart) "production_order"
  let ordinary ← output.getObjVal? "solution"
  let guillotine ← ordinary.getObjValAs? Bool "guillotine"
  let rawLayouts ← ordinary.getObjValAs? (List Json) "layouts"
  let kerfArea ← ordinary.getObjValAs? Nat "total_kerf_area"
  let wasteArea ← ordinary.getObjValAs? Nat "total_waste_area"
  unless result.certificate.check && Indexed.checkSheets constraints result && guillotine &&
      (groups.isEmpty || groups.length == result.demands.length) &&
      trees.length == result.layoutCount &&
      reportedUnplaced == result.demands.zipIdx.map (fun (d, i) => result.missing i d) do
    return false
  let mut order : List ProductionPart := []
  let mut sequence : List Nat := []
  let mut totalKerf := 0
  let mut totalWaste := 0
  for ((row, wireTree, rawLayout), layoutIndex) in (result.layouts.zip (trees.zip rawLayouts)).zipIdx do
    let some stock := result.stocks[row.stockIndex]? | throw "missing cut-tree stock source"
    let some sheet := constraints[row.stockIndex]? | throw "missing cut-tree sheet rules"
    let root := Region.mk sheet.trim.trim_left sheet.trim.trim_top
      (stock.extent.x - sheet.trim.trim_left - sheet.trim.trim_right)
      (stock.extent.y - sheet.trim.trim_top - sheet.trim.trim_bottom)
    let nodes ← wireTree.getObjValAs? (Array Json) "nodes"
    let first ← wireTree.getObjValAs? Axis "first_axis"
    let (tree, seen) ← (decodeTree nodes stock.gap (nodes.size + 1) 0).run []
    unless seen.length == nodes.size && tree.check stock.gap root &&
        (rules.cut_through_defects || sheet.defects.all
          (fun defect => tree.avoidsBlades stock.gap (Region.ofPiece defect))) &&
        checkStages rules first root tree do
      return false
    let parts := tree.parts
    unless row.demandIndices == parts.map Part.demand &&
        row.layout.pieces.length == parts.length &&
        (row.layout.pieces.zip parts).all (fun (placed, part) =>
          Region.ofPiece placed == part.region && (placed.rotation == "quarter") == part.rotated) do
      return false
    let used := (parts.map (fun part => part.region.area)).sum
    let waste := stock.extent.x * stock.extent.y - used
    let blade := tree.kerfArea stock.gap
    unless used == (← rawLayout.getObjValAs? Nat "used_area") &&
        waste == (← rawLayout.getObjValAs? Nat "waste_area") &&
        blade == (← rawLayout.getObjValAs? Nat "kerf_area") do
      return false
    totalKerf := totalKerf + blade
    totalWaste := totalWaste + waste
    order := order ++ parts.map (fun part => ⟨layoutIndex, part.node⟩)
    sequence := sequence ++ row.demandIndices
  return order == productionOrder && checkGroups groups result.demands [] sequence &&
    totalKerf == kerfArea && totalWaste == wasteArea

end Packing.Staged
