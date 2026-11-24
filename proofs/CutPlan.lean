import Saw
import Optimality

set_option warningAsError true

namespace Packing.CutPlan

open Lean Staged

private def maxExactUnits : Nat := 2 ^ 53

/-- Decode an exact nonnegative binary64 value in units of 2⁻¹⁶. -/
def exactDyadicUnits (json : Json) : Except String Nat := do
  let number ← json.getNum?
  let error := "exact binary64 certification requires nonnegative dyadic prices and costs (integers or multiples of 2^-k with k ≤ 16)"
  unless 0 ≤ number.mantissa do throw error
  let mut mantissa := number.mantissa.natAbs
  if mantissa == 0 then return 0
  let mut exponent := number.exponent
  for _ in [:number.exponent] do
    if mantissa % 10 != 0 then break
    mantissa := mantissa / 10
    exponent := exponent - 1
  unless exponent ≤ 16 do throw error
  let factor := 5 ^ exponent
  unless mantissa % factor == 0 do throw error
  let scaled := (mantissa / factor) * 2 ^ (16 - exponent)
  unless scaled ≤ maxExactUnits do throw "exact binary64 certification requires at most 2^53 scaled units"
  return scaled

def readPrice (options : Json) (key : String) (fallback : JsonNumber) : Except String Nat := do
  let value ← readDefault options key (none : Option Json)
  (exactDyadicUnits (value.getD (.num fallback))).mapError fun error =>
    s!"options.{key}: {error}"

def checkPrices (reported : Json) (prices : List (String × Nat)) : Except String Bool :=
  prices.allM fun (key, expected) =>
    return (← exactDyadicUnits (← reported.getObjVal? key)) == expected

/-- With nonnegative prices, a bounded total also bounds every product and partial sum. -/
private def checkTotalCost (plan : Json) (expected : Nat) : Except String Bool := do
  unless expected ≤ maxExactUnits do return false
  return (← exactDyadicUnits (← plan.getObjVal? "total_cost")) == expected

inductive BarStep where
  | cut (position : Nat) (pieceName : String)
  | fenceReset (length : Nat)
  deriving DecidableEq

instance : FromJson BarStep where
  fromJson? j := do
    match ← j.getObjValAs? String "kind" with
    | "cut" => return .cut (← j.getObjValAs? Nat "position") (← j.getObjValAs? String "piece_name")
    | "fence_reset" => return .fenceReset (← j.getObjValAs? Nat "new_position")
    | kind => throw s!"unknown bar step {kind}"

def BarStep.isCut : BarStep → Bool
  | .cut .. => true
  | .fenceReset _ => false

def BarStep.inBounds (capacity : Nat) : BarStep → Prop
  | .cut position _ => position ≤ capacity
  | .fenceReset length => 0 < length ∧ length ≤ capacity

instance (capacity : Nat) (step : BarStep) : Decidable (step.inBounds capacity) := by
  cases step <;> unfold BarStep.inBounds <;> infer_instance

/-- The stock itself provides the last piece's end when the bar is fully used. -/
def barSteps (kerf : Nat) (hasDrop : Bool) (cursor : Nat) (fence : Option Nat) :
    List (String × Nat) → List BarStep
  | [] => []
  | (name, length) :: rest =>
    if rest.isEmpty && !hasDrop then []
    else
      let position := cursor + length
      let reset := if fence == some length then [] else [.fenceReset length]
      reset ++ [.cut position name] ++ barSteps kerf hasDrop (position + kerf) (some length) rest

def replayBar (kerf capacity remaining : Nat) (pieces : List (String × Nat))
    (steps : List BarStep) (cuts resets : Nat) : Bool :=
  decide (linearLength kerf (pieces.map Prod.snd) + remaining = capacity ∧
    steps = barSteps kerf (remaining != 0) 0 none pieces ∧
    cuts = steps.countP BarStep.isCut ∧ resets = steps.countP (fun step => !step.isCut)) &&
  steps.all (fun step => decide (step.inBounds capacity))

theorem replayBar_preserves_length_and_counts (kerf capacity remaining : Nat)
    (pieces : List (String × Nat)) (steps : List BarStep) (cuts resets : Nat)
    (h : replayBar kerf capacity remaining pieces steps cuts resets = true) :
    linearLength kerf (pieces.map Prod.snd) + remaining = capacity ∧
    (∀ step ∈ steps, step.inBounds capacity) ∧
    steps = barSteps kerf (remaining != 0) 0 none pieces ∧
    cuts = steps.countP BarStep.isCut ∧ resets = steps.countP (fun step => !step.isCut) := by
  simp only [replayBar, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.2, h.1.2⟩

def checkCutPlan1D (input output : Json) : Except String Bool := do
  let problem ← input.getObjVal? "problem"
  let solution ← input.getObjVal? "solution"
  let options ← input.getObjVal? "options"
  let preset ← readDefault options "preset" "chop_saw"
  unless preset == "chop_saw" && (← output.getObjValAs? String "preset") == preset do return false
  let cutPrice ← readPrice options "cut_cost" 1
  let resetPrice ← readPrice options "fence_reset_cost" ⟨3, 1⟩
  unless ← checkPrices (← output.getObjVal? "effective_costs")
      [("cut_cost", cutPrice), ("fence_reset_cost", resetPrice)] do return false
  let certificate ← readCertificate .linear problem solution
  unless certificate.check do return false
  let plans ← output.getObjValAs? (List Json) "bar_plans"
  unless plans.length == certificate.layouts.length do return false
  let mut total := 0
  for ((layout, plan), index) in (certificate.layouts.zip plans).zipIdx do
    let some stock := certificate.stock.find? (fun s => s.name == layout.stock) | return false
    let some summary := layout.linear | return false
    let pieces := layout.pieces.map fun piece => (piece.name, piece.extent.x)
    let steps ← plan.getObjValAs? (List BarStep) "steps"
    let cuts ← plan.getObjValAs? Nat "num_cuts"
    let resets ← plan.getObjValAs? Nat "num_fence_resets"
    let cost := cuts * cutPrice + resets * resetPrice
    unless (← plan.getObjValAs? String "stock_name") == layout.stock &&
        (← plan.getObjValAs? Nat "bar_index_in_solution") == index &&
        replayBar stock.gap stock.bounds.x summary.remaining pieces steps cuts resets &&
        (← checkTotalCost plan cost) do return false
    total := total + cost
  checkTotalCost output total

inductive Preset where
  | table_saw | panel_saw | cnc_router
  deriving DecidableEq, FromJson

structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq

def Point.inBounds (point : Point) (sheet : Region) : Prop :=
  sheet.x ≤ point.x ∧ point.x ≤ sheet.x + sheet.width ∧
    sheet.y ≤ point.y ∧ point.y ≤ sheet.y + sheet.height

instance (point : Point) (sheet : Region) : Decidable (point.inBounds sheet) := by
  unfold Point.inBounds
  infer_instance

def distance (a b : Point) : Nat :=
  (a.x - b.x) + (b.x - a.x) + (a.y - b.y) + (b.y - a.y)

inductive SheetStep where
  | cut (axis : Axis) (position : Nat)
  | rotate
  | fenceReset (position : Nat)
  | lineCut (start finish : Point)
  | toolUp
  | toolDown
  | travel (finish : Point)
  deriving DecidableEq

def readPoint (j : Json) (x y : String) : Except String Point := do
  return ⟨← j.getObjValAs? Nat x, ← j.getObjValAs? Nat y⟩

instance : FromJson SheetStep where
  fromJson? j := do
    match ← j.getObjValAs? String "kind" with
    | "cut" => return .cut (← j.getObjValAs? Axis "axis") (← j.getObjValAs? Nat "position")
    | "rotate" => return .rotate
    | "fence_reset" => return .fenceReset (← j.getObjValAs? Nat "new_position")
    | "line_cut" => return .lineCut (← readPoint j "from_x" "from_y") (← readPoint j "to_x" "to_y")
    | "tool_up" => return .toolUp
    | "tool_down" => return .toolDown
    | "travel" => return .travel (← readPoint j "to_x" "to_y")
    | kind => throw s!"unknown sheet step {kind}"

def SheetStep.isRotation : SheetStep → Bool
  | .rotate => true
  | _ => false

def SheetStep.isReset : SheetStep → Bool
  | .fenceReset _ => true
  | _ => false

structure GuillotineCut where
  axis : Axis
  position : Nat

def sawCuts (steps : List SheetStep) : List GuillotineCut :=
  steps.filterMap fun step =>
    match step with
    | .cut axis position => some ⟨axis, position⟩
    | _ => none

def sawSteps (previous : Option GuillotineCut) : List GuillotineCut → List SheetStep
  | [] => []
  | cut :: rest =>
    let setup :=
      match previous with
      | none => []
      | some prior =>
        if prior.axis != cut.axis then [.rotate]
        else if prior.position != cut.position then [.fenceReset cut.position]
        else []
    setup ++ [.cut cut.axis cut.position] ++ sawSteps (some cut) rest

structure SawRegion where
  bounds : Region
  parts : List Region

def SawRegion.finished (region : SawRegion) : Bool :=
  region.parts.isEmpty || region.parts == [region.bounds]

def SawRegion.split (region : SawRegion) (cut : GuillotineCut) :
    Option (SawRegion × SawRegion) := do
  let start := Saw.lowCoordinate region.bounds cut.axis
  let stop := start + region.bounds.extent cut.axis
  let before := fun p : Region => Saw.lowCoordinate p cut.axis + p.extent cut.axis ≤ cut.position
  let after := fun p : Region => cut.position ≤ Saw.lowCoordinate p cut.axis
  if !(decide (start < cut.position ∧ cut.position < stop) &&
        region.parts.all (fun part => decide (before part ∨ after part))) then none
  else
    let offset := cut.position - start
    some (⟨region.bounds.low cut.axis offset, region.parts.filter (fun p => decide (before p))⟩,
      ⟨region.bounds.high cut.axis offset, region.parts.filter (fun p => decide (after p))⟩)

/-- Replay the legacy preorder using the first unfinished region on the stack. -/
def replaySaw (pending : List SawRegion) : List GuillotineCut → Bool
  | [] => pending.all SawRegion.finished
  | cut :: rest =>
    match pending.dropWhile SawRegion.finished with
    | [] => false
    | region :: tail =>
      match region.split cut with
      | none => false
      | some (low, high) => replaySaw (low :: high :: tail) rest

def outline (r : Region) : List SheetStep :=
  let tl : Point := ⟨r.x, r.y⟩
  let tr : Point := ⟨r.x + r.width, r.y⟩
  let bl : Point := ⟨r.x, r.y + r.height⟩
  let br : Point := ⟨r.x + r.width, r.y + r.height⟩
  [.lineCut tl tr, .lineCut tr br, .lineCut br bl, .lineCut bl tl]

def SheetStep.isLine : SheetStep → Bool
  | .lineCut .. => true
  | _ => false

def checkOutlines (parts : List Region) : List SheetStep → Bool
  | a :: b :: c :: d :: rest =>
    match parts.find? (fun part => outline part == [a, b, c, d]) with
    | none => false
    | some part => checkOutlines (parts.erase part) rest
  | steps => steps.isEmpty && parts.isEmpty

structure CncState where
  point : Point := ⟨0, 0⟩
  toolDown : Bool := false
  cuts : Nat := 0
  ups : Nat := 0
  downs : Nat := 0
  travel : Nat := 0

/-- CNC router certification enforces physical-stock bounds. On a sheet rooted at
    `(0, 0)`, every travel destination and cut endpoint must satisfy
    `0 ≤ x ≤ sheet.width` and `0 ≤ y ≤ sheet.height`. This rejects edge-kerf-relief
    paths that extend past the physical sheet boundary. -/
def CncLegal (sheet : Region) (parts : List Region) (state : CncState) (step : SheetStep) : Prop :=
  match step with
  | .toolDown => state.toolDown = false
  | .toolUp => state.toolDown = true
  | .travel finish => state.toolDown = false ∧ finish.inBounds sheet
  | .lineCut start finish =>
    state.toolDown = true ∧ state.point = start ∧ start.inBounds sheet ∧ finish.inBounds sheet ∧
      parts.any (fun part => (outline part).contains step) = true
  | _ => False

instance (sheet : Region) (parts : List Region) (state : CncState) (step : SheetStep) :
    Decidable (CncLegal sheet parts state step) := by
  cases step <;> unfold CncLegal <;> infer_instance

def CncState.advance (state : CncState) : SheetStep → CncState
  | .toolDown => { state with toolDown := true, downs := state.downs + 1 }
  | .toolUp => { state with toolDown := false, ups := state.ups + 1 }
  | .travel finish => { state with
      point := finish
      travel := min (2^64 - 1) (state.travel + distance state.point finish) }
  | .lineCut _ finish => { state with point := finish, cuts := state.cuts + 1 }
  | _ => state

def replayCnc (sheet : Region) (parts : List Region) (state : CncState) :
    List SheetStep → Option CncState
  | [] => some state
  | step :: rest =>
    if CncLegal sheet parts state step then replayCnc sheet parts (state.advance step) rest else none

def CncTrace (sheet : Region) (parts : List Region) (state : CncState) : List SheetStep → Prop
  | [] => True
  | step :: rest => CncLegal sheet parts state step ∧ CncTrace sheet parts (state.advance step) rest

def CncInvariant (sheet : Region) (state : CncState) : Prop :=
  state.point.inBounds sheet ∧ state.downs = state.ups + if state.toolDown then 1 else 0

private theorem cncAdvance_preserves (sheet : Region) (parts : List Region) (state : CncState)
    (step : SheetStep) (h : CncInvariant sheet state) (legal : CncLegal sheet parts state step) :
    CncInvariant sheet (state.advance step) := by
  cases step <;> simp [CncLegal] at legal
  all_goals obtain ⟨bounded, balance⟩ := h
  case toolUp =>
    simp [CncInvariant, CncState.advance, bounded, legal] at balance ⊢
    omega
  case toolDown =>
    simp [CncInvariant, CncState.advance, bounded, legal] at balance ⊢
    omega
  case travel =>
    exact ⟨legal.2, balance⟩
  case lineCut =>
    exact ⟨legal.2.2.2.1, balance⟩

private theorem replayCnc_sound (sheet : Region) (parts : List Region) (state result : CncState)
    (steps : List SheetStep) (initial : CncInvariant sheet state)
    (h : replayCnc sheet parts state steps = some result) :
    CncTrace sheet parts state steps ∧ CncInvariant sheet result := by
  induction steps generalizing state with
  | nil =>
    simp [replayCnc] at h
    exact ⟨trivial, h ▸ initial⟩
  | cons step rest ih =>
    by_cases legal : CncLegal sheet parts state step
    · have accepted := ih (state.advance step) (cncAdvance_preserves sheet parts state step initial legal)
        (by simpa [replayCnc, legal] using h)
      exact ⟨⟨legal, accepted.1⟩, accepted.2⟩
    · simp [replayCnc, legal] at h

/-- Each accepted prefix obeys tool state and endpoint rules. A completed
    trace ends inside the sheet with one lift per plunge. -/
theorem cncState_balanced_and_bounded (width height : Nat) (parts : List Region)
    (steps : List SheetStep) (result : CncState)
    (h : replayCnc ⟨0, 0, width, height⟩ parts {} steps = some result)
    (finished : result.toolDown = false) :
    CncTrace ⟨0, 0, width, height⟩ parts {} steps ∧
    result.point.inBounds ⟨0, 0, width, height⟩ ∧ result.downs = result.ups := by
  have initial : CncInvariant ⟨0, 0, width, height⟩ {} := by
    simp [CncInvariant, Point.inBounds]
  have accepted := replayCnc_sound _ _ _ _ _ initial h
  exact ⟨accepted.1, accepted.2.1, by simpa [finished] using accepted.2.2⟩

structure SheetCounts where
  num_cuts : Nat
  num_rotations : Nat
  num_fence_resets : Nat
  num_tool_ups : Nat
  travel_distance : Nat
  deriving DecidableEq, FromJson

structure SheetPrices where
  cut : Nat
  rotate : Nat
  reset : Nat
  tool : Nat
  travel : Nat

def SheetPrices.defaults : Preset → JsonNumber × JsonNumber × JsonNumber × JsonNumber
  | .table_saw => (2, ⟨5, 1⟩, 0, 0)
  | .panel_saw => (5, ⟨3, 1⟩, 0, 0)
  | .cnc_router => (0, 0, ⟨2, 1⟩, ⟨1, 2⟩)

def SheetPrices.resolve (preset : Preset) (options : Json) : Except String SheetPrices := do
  let (rotate, reset, tool, travel) := SheetPrices.defaults preset
  return ⟨← readPrice options "cut_cost" 1, ← readPrice options "rotate_cost" rotate,
    ← readPrice options "fence_reset_cost" reset, ← readPrice options "tool_up_down_cost" tool,
    ← readPrice options "travel_cost" travel⟩

def SheetPrices.cost (prices : SheetPrices) (counts : SheetCounts) : Nat :=
  counts.num_cuts * prices.cut + counts.num_rotations * prices.rotate +
    counts.num_fence_resets * prices.reset + counts.num_tool_ups * prices.tool +
    counts.travel_distance * prices.travel

def checkSheetSteps (preset : Preset) (sheet : Region) (parts : List Region)
    (steps : List SheetStep) (counts : SheetCounts) : Bool :=
  match preset with
  | .cnc_router =>
    match replayCnc sheet parts {} steps with
    | none => false
    | some state =>
      !state.toolDown && checkOutlines parts (steps.filter SheetStep.isLine) &&
        counts == ⟨state.cuts, 0, 0, state.ups, state.travel⟩
  | .table_saw | .panel_saw =>
    let cuts := sawCuts steps
    -- The legacy saw planner expands its root for edge-relief placements.
    let root := parts.foldl (fun r p => { r with
      width := max r.width (p.x + p.width), height := max r.height (p.y + p.height) }) sheet
    replaySaw [⟨root, parts⟩] cuts && steps == sawSteps none cuts &&
      counts == ⟨cuts.length, steps.countP SheetStep.isRotation,
        steps.countP SheetStep.isReset, 0, 0⟩

def checkCutPlan2D (input output : Json) : Except String Bool := do
  let solution ← input.getObjVal? "solution"
  let options ← input.getObjVal? "options"
  let preset ← readDefault options "preset" Preset.table_saw
  unless (← output.getObjValAs? Preset "preset") == preset do return false
  let prices ← SheetPrices.resolve preset options
  unless ← checkPrices (← output.getObjVal? "effective_costs")
      [("cut_cost", prices.cut), ("rotate_cost", prices.rotate), ("fence_reset_cost", prices.reset),
        ("tool_up_down_cost", prices.tool), ("travel_cost", prices.travel)] do return false
  let layouts ← solution.getObjValAs? (List Json) "layouts"
  let plans ← output.getObjValAs? (List Json) "sheet_plans"
  unless plans.length == layouts.length do return false
  let mut total := 0
  for ((layout, plan), index) in (layouts.zip plans).zipIdx do
    let name ← layout.getObjValAs? String "sheet_name"
    let extent ← readExtent .sheet layout
    let sheet : Region := ⟨0, 0, extent.x, extent.y⟩
    let pieces ← (← layout.getObjValAs? (List Json) "placements").mapM (readPiece .sheet)
    let parts := pieces.map Region.ofPiece
    let steps ← plan.getObjValAs? (List SheetStep) "steps"
    let counts ← fromJson? (α := SheetCounts) plan
    let cost := prices.cost counts
    unless (← plan.getObjValAs? String "sheet_name") == name &&
        (← plan.getObjValAs? Nat "sheet_index_in_solution") == index &&
        decide (0 < sheet.area ∧ extent.x < 2^32 ∧ extent.y < 2^32 ∧
          pieces.Pairwise (Separated 0)) &&
        parts.all (fun p => decide (0 < p.area ∧ p.x + p.width < 2^32 ∧ p.y + p.height < 2^32)) &&
        checkSheetSteps preset sheet parts steps counts &&
        (← checkTotalCost plan cost) do return false
    total := total + cost
  checkTotalCost output total

end Packing.CutPlan

open Lean

run_cmd do
  let standard := [`propext, `Quot.sound, `Classical.choice]
  for theoremName in [`Packing.CutPlan.replayBar_preserves_length_and_counts,
      `Packing.CutPlan.cncAdvance_preserves, `Packing.CutPlan.replayCnc_sound,
      `Packing.CutPlan.cncState_balanced_and_bounded] do
    for dependency in ← Lean.collectAxioms theoremName do
      unless standard.contains dependency do
        throwError "unexpected axiom {dependency} in {theoremName}"
