import Staged

set_option warningAsError true

namespace Packing.Saw

open Lean Staged

inductive Machine where
  | table_saw | panel_saw
  deriving DecidableEq, FromJson

inductive Accessory where
  | rip_fence | crosscut_stop | panel_stop
  deriving DecidableEq, FromJson

inductive Edge where
  | left | top | right | bottom
  deriving DecidableEq, FromJson

structure Setup where
  kind : Accessory
  distance : Nat
  deriving DecidableEq, FromJson

structure WorkpieceId where
  sheet_index : Nat
  bounds : Region
  deriving DecidableEq, FromJson

structure PartId where
  sheet_index : Nat
  placement_index : Nat
  deriving DecidableEq, FromJson

structure Workpiece where
  id : WorkpieceId
  parent : Option WorkpieceId
  created_by : Option Nat
  finished_part : Option PartId
  usable_offcut : Bool
  deriving DecidableEq, FromJson

structure Views where
  sheet_index_in_solution : Nat
  stock_index : Nat
  operation_ids : List Nat
  deriving DecidableEq, FromJson

structure Counts where
  cuts : Nat := 0
  initial_setups : Nat := 0
  setup_changes : Nat := 0
  rotations : Nat := 0
  handling : Nat := 0
  deriving DecidableEq, FromJson

structure Segment where
  from_x : Nat
  from_y : Nat
  to_x : Nat
  to_y : Nat
  deriving DecidableEq, FromJson

structure Cut where
  axis : Axis
  reference_edge : Edge
  setting : Nat
  kerf : Nat
  kerf_region : Region
  segment : Segment
  children : List WorkpieceId
  deriving FromJson

structure Options where
  machine : Machine := .table_saw
  batch_across_sheets : Bool := false
  min_usable_side : Nat := 0

instance : FromJson Options where
  fromJson? j := do
    return ⟨← readDefault j "machine" .table_saw, ← readDefault j "batch_across_sheets" false,
      ← readDefault j "min_usable_side" 0⟩

structure Operation where
  id : Nat
  workpiece : WorkpieceId
  depends_on : Option Nat
  action : Json
  deriving FromJson

structure SourceSheet where
  stock : Nat
  root : Region
  parts : List Region
  kerf : Nat
  relief : Bool

structure Source where
  sheets : List SourceSheet
  options : Options

def readSource (input : Json) : Except String Source := do
  let job ← input.getObjVal? "job"
  let options ← input.getObjValAs? Options "options"
  let problem ← job.getObjVal? "problem"
  let rawStocks ← problem.getObjValAs? (List Json) "sheets"
  let stocks ← rawStocks.mapM (readStock .sheet)
  let demands ← (← problem.getObjValAs? (List Json) "demands").mapM (readDemand .sheet)
  let stockIndices ← job.getObjValAs? (List Nat) "stock_indices"
  let demandIndices ← job.getObjValAs? (List (List Nat)) "demand_indices"
  let layouts ← job.getObjValAs? (List Json) "layouts"
  unless layouts.length == stockIndices.length && layouts.length == demandIndices.length do
    throw "saw job provenance arrays have different lengths"
  unless stocks.zipIdx.all (fun (stock, index) =>
      Indexed.limitFits stock.limit (stockIndices.count index)) &&
      demands.zipIdx.all (fun (demand, index) => demandIndices.flatten.count index ≤ demand.quantity) do
    throw "saw job exceeds source inventory or demand"
  let sheets ← (layouts.zip (stockIndices.zip demandIndices)).mapM fun (layout, stockIndex, ids) => do
    let some stock := stocks[stockIndex]? | throw "unknown saw stock source"
    let some rawStock := rawStocks[stockIndex]? | throw "missing saw stock"
    let extent ← readExtent .sheet layout
    let parts ← (← layout.getObjValAs? (List Json) "placements").mapM (readPiece .sheet)
    unless extent == stock.extent && parts.length == ids.length do
      throw "saw job layout dimensions or placement provenance differ from source"
    let rawStockGeometry := { stock with bounds := stock.extent, gap := 0 }
    let physical : Layout := ⟨stock.name, extent, parts, none⟩
    unless physical.check rawStockGeometry do
      throw "saw job part geometry lies outside physical stock or overlaps"
    for (part, index) in parts.zip ids do
      let some demand := demands[index]? | throw "unknown saw demand source"
      unless (part.rotation, part.extent) ∈ demand.orientations do
        throw "saw job part dimensions or rotation differ from source"
    let relief ← readDefault rawStock "edge_kerf_relief" false
    return ⟨stockIndex, ⟨0, 0, extent.x, extent.y⟩, parts.map Region.ofPiece, stock.gap, relief⟩
  return ⟨sheets, options⟩

def lowCoordinate (r : Region) (axis : Axis) : Nat :=
  match axis with | .vertical => r.x | .horizontal => r.y

def cutChildren (r : Region) (axis : Axis) (offset removed : Nat) : List Region :=
  [r.low axis offset, r.high axis (offset + removed)].filter (fun region => region.area != 0)

theorem all_children_area (r : Region) (axis : Axis) (offset removed : Nat)
    (h : offset + removed ≤ r.extent axis) :
    ((cutChildren r axis offset removed).map Region.area).sum + r.bladeArea axis removed =
      r.area := by
  have harea := cut_area r axis offset removed h
  simp only [cutChildren, List.filter_cons, List.filter_nil]
  by_cases hlow : (r.low axis offset).area = 0 <;>
    by_cases hhigh : (r.high axis (offset + removed)).area = 0 <;>
    simp_all [List.sum_cons]

def Edge.turns : Edge → Nat
  | .left => 0
  | .bottom => 1
  | .right => 2
  | .top => 3

def Edge.isLow : Edge → Bool
  | .left | .top => true
  | .right | .bottom => false

def Edge.aligned (edge : Edge) (axis : Axis) : Bool :=
  match axis, edge with
  | .vertical, .left | .vertical, .right | .horizontal, .top | .horizontal, .bottom => true
  | _, _ => false

def accessory (machine : Machine) (axis : Axis) : Accessory :=
  match machine, axis with
  | .panel_saw, _ => .panel_stop
  | .table_saw, .vertical => .rip_fence
  | .table_saw, .horizontal => .crosscut_stop

def bladeGeometry (r : Region) (axis : Axis) (start removed : Nat) : Region × Segment :=
  match axis with
  | .vertical =>
    (⟨start, r.y, removed, r.height⟩, ⟨start, r.y, start, r.y + r.height⟩)
  | .horizontal =>
    (⟨r.x, start, r.width, removed⟩, ⟨r.x, start, r.x + r.width, start⟩)

def checkSplit (source : SourceSheet) (id : WorkpieceId) (cut : Cut) : Bool :=
  let r := id.bounds
  let axis := cut.axis
  let start := lowCoordinate cut.kerf_region axis
  let low := lowCoordinate r axis
  let high := low + r.extent axis
  let removed := cut.kerf_region.extent axis
  let stop := start + removed
  let (band, segment) := bladeGeometry r axis start removed
  decide (low ≤ start ∧ stop ≤ high ∧ start < high ∧ low < stop ∧
      removed ≤ source.kerf ∧ 0 < cut.setting) &&
    (removed == source.kerf || (source.relief && (start == low || stop == high))) &&
    (source.kerf == 0 || removed != 0) &&
    cut.kerf == source.kerf && band == cut.kerf_region && segment == cut.segment &&
    cut.reference_edge.aligned axis &&
    cut.setting == (if cut.reference_edge.isLow then start - low else high - stop) &&
    cut.children == (cutChildren r axis (start - low) removed).map
      (fun region => ⟨id.sheet_index, region⟩)

/-- A verified scheduled cut accounts for the parent, including any clipped edge pass. -/
theorem checkSplit_conserves_area {source : SourceSheet} {id : WorkpieceId} {cut : Cut}
    (h : checkSplit source id cut = true) :
    (cut.children.map (fun child => child.bounds.area)).sum + cut.kerf_region.area =
      id.bounds.area := by
  simp only [checkSplit, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  let start := lowCoordinate cut.kerf_region cut.axis
  let offset := start - lowCoordinate id.bounds cut.axis
  let removed := cut.kerf_region.extent cut.axis
  have hposition : offset + removed ≤ id.bounds.extent cut.axis := by
    have hbounds := h.1.1.1.1.1.1.1.1
    dsimp [offset, start, removed]
    omega
  have hband :
      (bladeGeometry id.bounds cut.axis start removed).1 = cut.kerf_region := h.1.1.1.1.2
  have harea : cut.kerf_region.area = id.bounds.bladeArea cut.axis removed := by
    rw [← hband]
    cases cut.axis <;> simp [bladeGeometry, Region.area, Region.bladeArea, Region.crossExtent,
      Nat.mul_comm]
  rw [h.2, harea]
  simpa [List.map_map, Function.comp_def, offset, start, removed] using
    all_children_area id.bounds cut.axis offset removed hposition

def includes (outer inner : Region) : Bool :=
  decide (outer.x ≤ inner.x ∧ inner.x + inner.width ≤ outer.x + outer.width ∧
    outer.y ≤ inner.y ∧ inner.y + inner.height ≤ outer.y + outer.height)

def bladeClears (parts : List Region) (parent : Region) (cut : Cut) : Bool :=
  let start := lowCoordinate cut.kerf_region cut.axis
  let stop := start + cut.kerf_region.extent cut.axis
  parts.all fun part =>
    !includes parent part ||
      decide (lowCoordinate part cut.axis + part.extent cut.axis ≤ start ∨
        stop ≤ lowCoordinate part cut.axis)

structure Trace where
  id : WorkpieceId
  parent : Option WorkpieceId
  cut : Option Nat

structure State where
  history : List Trace
  live : List (WorkpieceId × Nat)
  active : Option WorkpieceId := none
  setup : Option Setup := none
  accessories : List Accessory := []
  counts : Counts := {}
  previousSheet : Nat := 0

def State.apply (state : State) (source : Source) (i : Nat) (op : Operation) :
    Except String (Option State) := do
  let id := op.workpiece
  let some (_, turns) := state.live.find? (fun (piece, _) => piece == id) | return none
  let some trace := state.history.find? (fun entry => entry.id == id) | return none
  let some sheet := source.sheets[id.sheet_index]? | return none
  unless i == op.id && op.depends_on == trace.cut &&
      (source.options.batch_across_sheets || state.previousSheet ≤ id.sheet_index) do
    return none
  let state := { state with previousSheet := id.sheet_index }
  let kind ← op.action.getObjValAs? String "kind"
  if kind == "handle" then
    if state.active.isSome then return none
    return some { state with
      active := some id
      counts := { state.counts with handling := state.counts.handling + 1 } }
  unless state.active == some id do return none
  match kind with
  | "rotate" =>
    let requested ← op.action.getObjValAs? Nat "quarter_turns"
    unless requested < 4 && requested != turns do return none
    return some { state with
      live := state.live.map (fun pair => if pair.1 == id then (id, requested) else pair)
      counts := { state.counts with rotations := state.counts.rotations + 1 } }
  | "setup" =>
    let setup ← op.action.getObjValAs? Setup "setup"
    let initial ← op.action.getObjValAs? Bool "initial"
    unless state.setup != some setup && initial == !state.accessories.contains setup.kind do
      return none
    let counts := if initial then { state.counts with initial_setups := state.counts.initial_setups + 1 }
      else { state.counts with setup_changes := state.counts.setup_changes + 1 }
    return some { state with setup := some setup, accessories := setup.kind :: state.accessories, counts }
  | "cut" =>
    let cut ← fromJson? (α := Cut) op.action
    let setup : Setup := ⟨accessory source.options.machine cut.axis, cut.setting⟩
    unless state.setup == some setup && turns == cut.reference_edge.turns &&
        checkSplit sheet id cut && bladeClears sheet.parts id.bounds cut &&
        cut.children.all (fun child => !state.history.any (fun previous => previous.id == child)) do
      return none
    return some { state with
      active := none
      live := (state.live.filter (fun pair => pair.1 != id)) ++ cut.children.map (·, turns)
      history := state.history ++ cut.children.map (fun child => ⟨child, some id, some i⟩)
      counts := { state.counts with cuts := state.counts.cuts + 1 } }
  | _ => throw s!"unknown saw operation {kind}"

def checkSaw (input output : Json) : Except String Bool := do
  let source ← readSource input
  let schema ← output.getObjValAs? Nat "schema_version"
  let machine ← output.getObjValAs? Machine "machine"
  let batched ← output.getObjValAs? Bool "batch_across_sheets"
  let operations ← output.getObjValAs? (List Operation) "operations"
  let reportedCounts ← output.getObjValAs? Counts "counts"
  let workpieces ← output.getObjValAs? (List Workpiece) "workpieces"
  let views ← output.getObjValAs? (List Views) "sheet_views"
  unless schema == 1 && machine == source.options.machine &&
      batched == source.options.batch_across_sheets do return false
  let roots := source.sheets.zipIdx.map (fun (sheet, index) => WorkpieceId.mk index sheet.root)
  let mut state : State :=
    { history := roots.map (fun id => ⟨id, none, none⟩), live := roots.map (·, 0) }
  for (operation, index) in operations.zipIdx do
    let some next ← state.apply source index operation | return false
    state := next
  unless state.active.isNone && reportedCounts == state.counts &&
      workpieces.length == state.history.length &&
      decide ((workpieces.map Workpiece.id).Nodup) do return false
  let available := state.live.map Prod.fst
  for piece in workpieces do
    let id := piece.id
    let some trace := state.history.find? (fun trace => trace.id == id) | return false
    let some sheet := source.sheets[id.sheet_index]? | return false
    let finished := (sheet.parts.zipIdx.find? (fun (part, _) => part == id.bounds)).map
      (fun (_, index) => PartId.mk id.sheet_index index)
    let usable := available.contains id && finished.isNone &&
      decide (source.options.min_usable_side ≤ id.bounds.width ∧
        source.options.min_usable_side ≤ id.bounds.height)
    unless piece.parent == trace.parent && piece.created_by == trace.cut &&
        piece.finished_part == finished && piece.usable_offcut == usable do return false
  for (sheet, index) in source.sheets.zipIdx do
    unless sheet.parts.all (fun bounds => available.contains ⟨index, bounds⟩) do return false
  return views == source.sheets.zipIdx.map fun (sheet, index) =>
    ⟨index, sheet.stock, (operations.filter
      (fun operation => operation.workpiece.sheet_index == index)).map Operation.id⟩

end Packing.Saw
