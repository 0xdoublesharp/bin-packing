import Saw
import Optimality

set_option warningAsError true

namespace Packing.Reuse

open Lean Staged

private def maxExactUnits : Nat := 2 ^ 53

/-- Decode an exact nonnegative binary64 value in units of 2⁻¹⁶. -/
def exactDyadicUnits (json : Json) : Except String Nat := do
  let number ← json.getNum?
  let error := "exact binary64 certification requires nonnegative dyadic prices, weights, and costs (integers or multiples of 2^-k with k ≤ 16)"
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

structure ForecastPart2D where
  width : Nat
  height : Nat
  quantity : Nat
  can_rotate : Bool
  weight : Nat

instance : FromJson ForecastPart2D where
  fromJson? j := do
    return ⟨← j.getObjValAs? Nat "width", ← j.getObjValAs? Nat "height",
      ← j.getObjValAs? Nat "quantity", ← j.getObjValAs? Bool "can_rotate",
      ← exactDyadicUnits (← j.getObjVal? "weight")⟩

structure ReuseForecast2D where
  demands : List ForecastPart2D
  deriving FromJson

structure ReuseOptions2D where
  max_candidate_solves : Nat := 6
  max_future_parts : Nat := 256
  max_sheet_count : Option Nat := none
  max_material_cost : Option Nat := none

instance : FromJson ReuseOptions2D where
  fromJson? j := do
    let cost ← readDefault j "max_material_cost" (none : Option Json)
    return ⟨← readDefault j "max_candidate_solves" 6,
      ← readDefault j "max_future_parts" 256, ← readDefault j "max_sheet_count" none,
      ← cost.mapM exactDyadicUnits⟩

structure RecoverableOffcut2D where
  workpiece : Saw.WorkpieceId
  stock_index : Nat
  kerf : Nat
  deriving FromJson

structure ReusePlacement2D where
  forecast_index : Nat
  offcut_index : Nat
  bounds : Region
  rotated : Bool
  deriving FromJson

structure ReuseEvaluation2D where
  weighted_fulfillment : Nat
  fulfilled_counts : List Nat
  offcuts : List RecoverableOffcut2D
  placements : List ReusePlacement2D
  evaluation_truncated : Bool

instance : FromJson ReuseEvaluation2D where
  fromJson? j := do
    return ⟨← exactDyadicUnits (← j.getObjVal? "weighted_fulfillment"),
      ← j.getObjValAs? (List Nat) "fulfilled_counts",
      ← j.getObjValAs? (List RecoverableOffcut2D) "offcuts",
      ← j.getObjValAs? (List ReusePlacement2D) "placements",
      ← j.getObjValAs? Bool "evaluation_truncated"⟩

structure ReuseSolution2D where
  solution : Json
  job : Json
  baseline_evaluation : Json
  evaluation : Json
  baseline_sheet_count : Nat
  baseline_material_cost : Nat
  candidate_solves : Nat
  material_rejections : Nat
  physical_rejections : Nat

instance : FromJson ReuseSolution2D where
  fromJson? j := do
    return ⟨← j.getObjVal? "solution", ← j.getObjVal? "job",
      ← j.getObjVal? "baseline_evaluation", ← j.getObjVal? "evaluation",
      ← j.getObjValAs? Nat "baseline_sheet_count",
      ← exactDyadicUnits (← j.getObjVal? "baseline_material_cost"),
      ← j.getObjValAs? Nat "candidate_solves", ← j.getObjValAs? Nat "material_rejections",
      ← j.getObjValAs? Nat "physical_rejections"⟩

def Region.within (outer inner : Region) : Prop :=
  outer.x ≤ inner.x ∧ inner.x + inner.width ≤ outer.x + outer.width ∧
  outer.y ≤ inner.y ∧ inner.y + inner.height ≤ outer.y + outer.height

instance (outer inner : Region) : Decidable (Region.within outer inner) := by
  unfold Region.within
  infer_instance

def Region.disjoint (a b : Region) : Prop :=
  AxisSeparated 0 a.x a.width b.x b.width ∨ AxisSeparated 0 a.y a.height b.y b.height

instance : DecidableRel Region.disjoint := fun a b => by
  unfold Region.disjoint AxisSeparated
  infer_instance

def OffcutOnSheet (sheet : Saw.SourceSheet) (offcut : RecoverableOffcut2D) : Prop :=
  let r := offcut.workpiece.bounds
  offcut.stock_index = sheet.stock ∧ offcut.kerf = sheet.kerf ∧
    Region.within sheet.root r ∧ 0 < r.area ∧
    ∀ part ∈ sheet.parts, Region.disjoint r part

def OffcutsSeparated (a b : RecoverableOffcut2D) : Prop :=
  a.workpiece.sheet_index = b.workpiece.sheet_index →
    Region.disjoint a.workpiece.bounds b.workpiece.bounds

instance : DecidableRel OffcutsSeparated := fun a b => by
  unfold OffcutsSeparated
  infer_instance

def checkOffcut (sheets : List Saw.SourceSheet) (offcut : RecoverableOffcut2D) : Bool :=
  match sheets[offcut.workpiece.sheet_index]? with
  | none => false
  | some sheet =>
    let r := offcut.workpiece.bounds
    decide (offcut.stock_index = sheet.stock ∧ offcut.kerf = sheet.kerf ∧
      Region.within sheet.root r ∧ 0 < r.area) &&
      sheet.parts.all (fun part => decide (Region.disjoint r part))

def checkOffcuts (sheets : List Saw.SourceSheet) (offcuts : List RecoverableOffcut2D) : Bool :=
  offcuts.all (checkOffcut sheets) && decide (offcuts.Pairwise OffcutsSeparated)

def reuseSawInput (job : Json) : Json :=
  Json.mkObj [("job", job), ("options", Json.mkObj [("machine", toJson "table_saw"),
    ("batch_across_sheets", toJson false), ("min_usable_side", toJson (0 : Nat))])]

def replaySawOperations (source : Saw.Source) (operations : List Saw.Operation) :
    Except String (Option Saw.State) := do
  let roots := source.sheets.zipIdx.map (fun (sheet, index) => Saw.WorkpieceId.mk index sheet.root)
  let mut state : Saw.State :=
    { history := roots.map (fun id => ⟨id, none, none⟩), live := roots.map (·, 0) }
  for (operation, index) in operations.zipIdx do
    let some next ← state.apply source index operation | return none
    state := next
  return some state

private def terminalUsable (source : Saw.Source) (state : Saw.State) : List Saw.WorkpieceId :=
  (state.live.map Prod.fst).filter fun id =>
    match source.sheets[id.sheet_index]? with
    | none => false
    | some sheet => !sheet.parts.contains id.bounds

/-- Verify the saw certificate, then derive usable offcuts from its final live state. -/
def replaySawPlan (job : Json) (sawPlan : Json) : Except String (Option (List Saw.WorkpieceId)) := do
  let input := reuseSawInput job
  unless ← Saw.checkSaw input sawPlan do return none
  let source ← Saw.readSource input
  let operations ← sawPlan.getObjValAs? (List Saw.Operation) "operations"
  let some state ← replaySawOperations source operations | return none
  return some (terminalUsable source state)

def checkSawOffcuts (liveUsable : List Saw.WorkpieceId) (offcuts : List RecoverableOffcut2D) : Bool :=
  let ids := offcuts.map (·.workpiece)
  ids.all liveUsable.contains && decide ids.Nodup

/-- Each accepted offcut is a distinct live workpiece in the verified final saw state
    and its bounds do not identify a finished part. -/
theorem offcuts_from_verified_saw_workpieces
    (job sawPlan : Json) (liveUsable : List Saw.WorkpieceId) (offcuts : List RecoverableOffcut2D)
    (replayed : replaySawPlan job sawPlan = .ok (some liveUsable))
    (accepted : checkSawOffcuts liveUsable offcuts = true) :
    Saw.checkSaw (reuseSawInput job) sawPlan = .ok true ∧
    (offcuts.map (·.workpiece)).Nodup ∧
    ∃ source operations state,
      Saw.readSource (reuseSawInput job) = .ok source ∧
      sawPlan.getObjValAs? (List Saw.Operation) "operations" = .ok operations ∧
      replaySawOperations source operations = .ok (some state) ∧
      ∀ offcut ∈ offcuts, ∃ turns sheet,
        (offcut.workpiece, turns) ∈ state.live ∧
        source.sheets[offcut.workpiece.sheet_index]? = some sheet ∧
        offcut.workpiece.bounds ∉ sheet.parts := by
  cases checked : Saw.checkSaw (reuseSawInput job) sawPlan <;>
    simp [replaySawPlan, checked, bind, Except.bind] at replayed
  rename_i verified
  cases verified <;> simp [pure, Except.pure] at replayed
  cases readSource : Saw.readSource (reuseSawInput job) <;> simp [readSource] at replayed
  rename_i source
  cases readOperations : sawPlan.getObjValAs? (List Saw.Operation) "operations" <;>
    simp [readOperations] at replayed
  rename_i operations
  cases final : replaySawOperations source operations <;> simp [final] at replayed
  rename_i result
  cases result <;> simp at replayed
  rename_i state
  subst liveUsable
  simp only [checkSawOffcuts, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem, decide_eq_true_eq] at accepted
  refine ⟨rfl, accepted.2, source, operations, state, rfl, rfl, final, ?_⟩
  intro offcut member
  have usable := accepted.1 offcut.workpiece (List.mem_map_of_mem member)
  simp only [terminalUsable, List.mem_filter, List.mem_map] at usable
  obtain ⟨⟨⟨_, turns⟩, live, rfl⟩, nonpart⟩ := usable
  cases sheet : source.sheets[offcut.workpiece.sheet_index]? with
  | none => simp [sheet] at nonpart
  | some found => exact ⟨turns, found, live, rfl, by simpa [sheet] using nonpart⟩

private theorem checkOffcut_sound (sheets : List Saw.SourceSheet) (offcut : RecoverableOffcut2D)
    (h : checkOffcut sheets offcut = true) :
    ∃ sheet, sheets[offcut.workpiece.sheet_index]? = some sheet ∧ OffcutOnSheet sheet offcut := by
  cases hs : sheets[offcut.workpiece.sheet_index]? with
  | none => simp [checkOffcut, hs] at h
  | some sheet =>
    exact ⟨sheet, rfl, by
      simpa [checkOffcut, OffcutOnSheet, hs, Bool.and_eq_true, and_assoc] using h⟩

/-- Positive offcuts occupy half-open regions inside their physical sheet.
    Their edges may meet the sheet boundary or another rectangle's edge. -/
theorem offcuts_disjoint_from_parts_and_each_other
    (sheets : List Saw.SourceSheet) (offcuts : List RecoverableOffcut2D)
    (h : checkOffcuts sheets offcuts = true) :
    (∀ offcut ∈ offcuts, ∃ sheet,
      sheets[offcut.workpiece.sheet_index]? = some sheet ∧ OffcutOnSheet sheet offcut) ∧
    offcuts.Pairwise OffcutsSeparated := by
  simp only [checkOffcuts, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun offcut hm => checkOffcut_sound sheets offcut (h.1 offcut hm), h.2⟩

def ReusePlacement2D.piece (placement : ReusePlacement2D) : Piece :=
  let r := placement.bounds
  ⟨"", ⟨r.x, r.y, 0⟩, ⟨r.width, r.height, 1⟩, if placement.rotated then "quarter" else "identity"⟩

def FutureFits (sheet : Saw.SourceSheet) (offcut : RecoverableOffcut2D)
    (demand : ForecastPart2D) (placement : ReusePlacement2D) : Prop :=
  let r := placement.bounds
  let outer := offcut.workpiece.bounds
  let right := r.x + r.width
  let bottom := r.y + r.height
  Region.within outer r ∧
    (right = outer.x + outer.width ∨ right + sheet.kerf ≤ outer.x + outer.width ∨
      sheet.relief = true) ∧
    (bottom = outer.y + outer.height ∨ bottom + sheet.kerf ≤ outer.y + outer.height ∨
      sheet.relief = true) ∧
    0 < r.area ∧ 0 < demand.weight ∧
    (if placement.rotated then
      demand.can_rotate = true ∧ r.width = demand.height ∧ r.height = demand.width
    else r.width = demand.width ∧ r.height = demand.height)

instance (sheet : Saw.SourceSheet) (offcut : RecoverableOffcut2D) (demand : ForecastPart2D)
    (placement : ReusePlacement2D) : Decidable (FutureFits sheet offcut demand placement) := by
  unfold FutureFits
  split <;> infer_instance

def FutureSeparated (offcuts : List RecoverableOffcut2D) (a b : ReusePlacement2D) : Prop :=
  a.offcut_index = b.offcut_index →
    ∀ offcut, offcuts[a.offcut_index]? = some offcut → Separated offcut.kerf a.piece b.piece

instance (offcuts : List RecoverableOffcut2D) : DecidableRel (FutureSeparated offcuts) := fun a b => by
  unfold FutureSeparated
  cases offcuts[a.offcut_index]? <;> simp <;> infer_instance

def checkFuturePlacement (sheets : List Saw.SourceSheet) (forecast : ReuseForecast2D)
    (offcuts : List RecoverableOffcut2D) (placement : ReusePlacement2D) : Bool :=
  match offcuts[placement.offcut_index]?, forecast.demands[placement.forecast_index]? with
  | some offcut, some demand =>
    match sheets[offcut.workpiece.sheet_index]? with
    | some sheet => decide (offcut.kerf = sheet.kerf ∧ FutureFits sheet offcut demand placement)
    | none => false
  | _, _ => false

def checkFuturePlacements (sheets : List Saw.SourceSheet) (forecast : ReuseForecast2D)
    (offcuts : List RecoverableOffcut2D) (placements : List ReusePlacement2D) : Bool :=
  placements.all (checkFuturePlacement sheets forecast offcuts) &&
    decide (placements.Pairwise (FutureSeparated offcuts))

/-- Every placement uses a known forecast and offcut, and no two placements on
    that offcut can occupy the same kerf-expanded cell. -/
theorem future_placements_valid_and_disjoint
    (sheets : List Saw.SourceSheet) (forecast : ReuseForecast2D)
    (offcuts : List RecoverableOffcut2D) (placements : List ReusePlacement2D)
    (h : checkFuturePlacements sheets forecast offcuts placements = true) :
    (∀ placement ∈ placements, ∃ offcut demand sheet,
      offcuts[placement.offcut_index]? = some offcut ∧
      forecast.demands[placement.forecast_index]? = some demand ∧
      sheets[offcut.workpiece.sheet_index]? = some sheet ∧
      offcut.kerf = sheet.kerf ∧ FutureFits sheet offcut demand placement) ∧
    placements.Pairwise (FutureSeparated offcuts) := by
  simp only [checkFuturePlacements, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  intro placement hm
  have hp := h.1 placement hm
  cases ho : offcuts[placement.offcut_index]? with
  | none => simp [checkFuturePlacement, ho] at hp
  | some offcut =>
    cases hd : forecast.demands[placement.forecast_index]? with
    | none => simp [checkFuturePlacement, ho, hd] at hp
    | some demand =>
      cases hs : sheets[offcut.workpiece.sheet_index]? with
      | none => simp [checkFuturePlacement, ho, hd, hs] at hp
      | some sheet =>
        exact ⟨offcut, demand, sheet, rfl, rfl, hs, by
          simpa [checkFuturePlacement, ho, hd, hs] using hp⟩

def fulfilledAt (placements : List ReusePlacement2D) (index : Nat) : Nat :=
  placements.countP (fun placement => placement.forecast_index == index)

def weightedFulfillment (forecast : ReuseForecast2D) (counts : List Nat) : Nat :=
  ((forecast.demands.zip counts).map (fun (demand, count) => demand.weight * count)).sum

def checkFulfilled (forecast : ReuseForecast2D) (evaluation : ReuseEvaluation2D) : Bool :=
  let count := fulfilledAt evaluation.placements
  let indexed := forecast.demands.zipIdx
  let total := weightedFulfillment forecast evaluation.fulfilled_counts
  decide (evaluation.fulfilled_counts = indexed.map (fun (_, index) => count index) ∧
    evaluation.weighted_fulfillment = total ∧ total ≤ maxExactUnits) &&
    indexed.all (fun (demand, index) => decide (count index ≤ demand.quantity))

theorem fulfilled_accounting_sound (forecast : ReuseForecast2D) (evaluation : ReuseEvaluation2D)
    (h : checkFulfilled forecast evaluation = true) :
    evaluation.fulfilled_counts.length = forecast.demands.length ∧
    (∀ index demand, forecast.demands[index]? = some demand →
      evaluation.fulfilled_counts[index]? = some (fulfilledAt evaluation.placements index) ∧
      fulfilledAt evaluation.placements index ≤ demand.quantity) ∧
    evaluation.weighted_fulfillment = weightedFulfillment forecast evaluation.fulfilled_counts := by
  simp only [checkFulfilled, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨by simp [h.1.1], ?_, h.1.2.1⟩
  intro index demand hd
  have hi : forecast.demands.zipIdx[index]? = some (demand, index) := by
    simp [List.getElem?_zipIdx, hd]
  refine ⟨by simp [h.1.1, hi], h.2 _ (List.mem_of_getElem? hi)⟩

def checkLimits (forecast : ReuseForecast2D) (options : ReuseOptions2D) : Bool :=
  decide (1 ≤ options.max_candidate_solves ∧ options.max_candidate_solves ≤ 8 ∧
    1 ≤ options.max_future_parts ∧ options.max_future_parts ≤ 512 ∧
    forecast.demands.length ≤ 64 ∧ (forecast.demands.map (·.quantity)).sum ≤ 4096) &&
  forecast.demands.all fun part =>
    decide (0 < part.width ∧ part.width ≤ 2^30 ∧ 0 < part.height ∧ part.height ≤ 2^30 ∧
      part.weight ≤ maxExactUnits)

def readJob (job : Json) : Except String Saw.Source :=
  Saw.readSource (reuseSawInput job)

def stockPrices (problem : Json) : Except String (List Nat) := do
  let stock ← problem.getObjValAs? (List Json) "sheets"
  stock.mapM (fun row => do exactDyadicUnits (← readDefault row "cost" (toJson (1 : Nat))))

private structure StockIdentity where
  name : String
  extent : Axes
  kerf : Nat
  limit : Option Nat
  relief : Bool
  price : Nat
  deriving DecidableEq

private structure DemandIdentity where
  name : String
  extent : Axes
  quantity : Nat
  orientations : List (String × Axes)
  deriving DecidableEq

private def problemSignature (problem : Json) :
    Except String (List StockIdentity × List DemandIdentity) := do
  let rawStocks ← problem.getObjValAs? (List Json) "sheets"
  let stocks ← (rawStocks.zip (← stockPrices problem)).mapM fun (raw, price) => do
    let stock ← readStock .sheet raw
    let relief ← readDefault raw "edge_kerf_relief" false
    return ⟨stock.name, stock.extent, stock.gap, stock.limit, relief, price⟩
  let demands ← (← problem.getObjValAs? (List Json) "demands").mapM fun raw => do
    let demand ← readDemand .sheet raw
    return ⟨demand.name, demand.extent, demand.quantity, demand.orientations⟩
  return (stocks, demands)

def materialCost (source : Saw.Source) (prices : List Nat) : Except String Nat := do
  let values ← source.sheets.mapM fun sheet => do
    let some price := prices[sheet.stock]? | throw "unknown priced stock"
    return price
  let total := values.sum
  unless total ≤ maxExactUnits do
    throw "exact binary64 certification requires material totals of at most 2^53 scaled units"
  return total

def checkEvaluation (job sawPlan : Json) (forecast : ReuseForecast2D) (options : ReuseOptions2D)
    (output : Json) : Except String Bool := do
  let source ← readJob job
  let prices ← stockPrices (← job.getObjVal? "problem")
  let cost ← materialCost source prices
  let evaluation ← fromJson? (α := ReuseEvaluation2D) output
  let some liveUsable ← replaySawPlan job sawPlan | return false
  let attempts := ((forecast.demands.filter (fun demand => demand.weight != 0)).map (·.quantity)).sum
  return checkLimits forecast options &&
    decide (source.sheets.length ≤ 32 ∧ (source.sheets.map (·.parts.length)).sum ≤ 128) &&
    source.sheets.all (fun sheet => some sheet.kerf == (source.sheets.head?.map (·.kerf))) &&
    Indexed.limitFits options.max_sheet_count source.sheets.length &&
    Indexed.limitFits options.max_material_cost cost &&
    decide (evaluation.placements.length ≤ options.max_future_parts) &&
    (!evaluation.evaluation_truncated || decide (options.max_future_parts < attempts)) &&
    checkSawOffcuts liveUsable evaluation.offcuts &&
    checkOffcuts source.sheets evaluation.offcuts &&
    checkFuturePlacements source.sheets forecast evaluation.offcuts evaluation.placements &&
    checkFulfilled forecast evaluation

def checkReuseEvaluation (input output : Json) : Except String Bool := do
  checkEvaluation (← input.getObjVal? "job") (← input.getObjVal? "saw_plan")
    (← input.getObjValAs? ReuseForecast2D "forecast")
    (← input.getObjValAs? ReuseOptions2D "options") output

def checkSelected (problem : Json) (result : ReuseSolution2D) (prices : List Nat) :
    Except String Bool := do
  let ordinary := result.solution
  let job := result.job
  let indexed ← Indexed.readIndexed .sheet problem <| Json.mkObj [
    ("solution", ordinary), ("stock_indices", ← job.getObjVal? "stock_indices"),
    ("demand_indices", ← job.getObjVal? "demand_indices")]
  unless indexed.certificate.check do return false
  let layouts ← ordinary.getObjValAs? (List Json) "layouts"
  let sawLayouts ← job.getObjValAs? (List Json) "layouts"
  let geometry ← layouts.mapM fun layout => do
    return Json.mkObj [("width", ← layout.getObjVal? "width"),
      ("height", ← layout.getObjVal? "height"), ("placements", ← layout.getObjVal? "placements")]
  unless geometry == sawLayouts do return false
  let mut total := 0
  for (row, layout) in indexed.layouts.zip layouts do
    let some price := prices[row.stockIndex]? | return false
    let reported ← exactDyadicUnits (← layout.getObjVal? "cost")
    unless reported == price do return false
    total := total + price
  return total ≤ maxExactUnits && total == (← exactDyadicUnits (← ordinary.getObjVal? "total_cost"))

/-- A reuse solution needs a `saw_plan` for its selected job. Supply a
    `baseline_job` and `baseline_saw_plan` to witness a different baseline job.
    If `baseline_job` is absent, the baseline plan defaults to `saw_plan`. -/
def checkReuseSolution (input output : Json) : Except String Bool := do
  let problem ← input.getObjVal? "problem"
  let sawPlan ← input.getObjVal? "saw_plan"
  let forecast ← input.getObjValAs? ReuseForecast2D "forecast"
  let limits ← input.getObjValAs? ReuseOptions2D "options"
  let result ← fromJson? (α := ReuseSolution2D) output
  let baselineJob ← readDefault input "baseline_job" (none : Option Json)
  let baselineSawPlan ← readDefault input "baseline_saw_plan" (none : Option Json)
  let baselineSawPlan ← match baselineSawPlan, baselineJob with
    | some plan, _ => pure plan
    | none, none => pure sawPlan
    | none, some _ => throw "baseline_saw_plan is required when baseline_job is provided"
  let baselineJob := baselineJob.getD result.job
  let signature ← problemSignature problem
  let selectedSignature ← problemSignature (← result.job.getObjVal? "problem")
  let baselineSignature ← problemSignature (← baselineJob.getObjVal? "problem")
  unless decide (selectedSignature = signature ∧ baselineSignature = signature) &&
      decide (0 < result.candidate_solves ∧ result.candidate_solves ≤ limits.max_candidate_solves ∧
        result.material_rejections + result.physical_rejections < result.candidate_solves) do
    return false
  let prices ← stockPrices problem
  let baseline ← readJob baselineJob
  unless baseline.sheets.length == result.baseline_sheet_count &&
      (← materialCost baseline prices) == result.baseline_material_cost do return false
  let effective := { limits with
    max_sheet_count := some (limits.max_sheet_count.getD result.baseline_sheet_count)
    max_material_cost := some (limits.max_material_cost.getD result.baseline_material_cost) }
  return (← checkSelected problem result prices) &&
    (← checkEvaluation baselineJob baselineSawPlan forecast effective result.baseline_evaluation) &&
    (← checkEvaluation result.job sawPlan forecast effective result.evaluation)

end Packing.Reuse

open Lean

run_cmd do
  let standard := [`propext, `Quot.sound, `Classical.choice]
  for theoremName in [`Packing.Reuse.checkOffcut_sound,
      `Packing.Reuse.offcuts_from_verified_saw_workpieces,
      `Packing.Reuse.offcuts_disjoint_from_parts_and_each_other,
      `Packing.Reuse.future_placements_valid_and_disjoint,
      `Packing.Reuse.fulfilled_accounting_sound] do
    for dependency in ← Lean.collectAxioms theoremName do
      unless standard.contains dependency do
        throwError "unexpected axiom {dependency} in {theoremName}"
