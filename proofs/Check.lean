import Staged
import Optimality
import ExactLinear
import ExactGrid
import Loading
import Circles
import Saw
import Polygons
import Orthogonal
import Sloped
import Bounds
import Optimization
import Reuse
import CutPlan
import IrregularExact
import AccountingAndSemantics

set_option warningAsError true

open Lean Packing

run_cmd do
  let standard := [`propext, `Quot.sound, `Classical.choice]
  let guarantees := [
    `Packing.Certificate.check_iff, `Packing.Layout.physical, `Packing.checkLinear_sound,
    `Packing.Indexed.checkSheet_iff, `Packing.Indexed.checkPayload_iff,
    `Packing.Indexed.checkShortages_iff, `Packing.Staged.Tree.conserves_area,
    `Packing.Staged.Tree.avoidsBlades_iff, `Packing.Saw.checkSplit_conserves_area,
    `Packing.Loading.checkNesting_iff, `Packing.Loading.nested_items_under_top,
    `Packing.Loading.axle_conserves_weight, `Packing.Loading.reaction_ceiling_within_cap,
    `Packing.Circles.clear_disjoint, `Packing.Circles.boundary_contains_part,
    `Packing.Polygons.checkPair_disjoint, `Packing.Polygons.hull_inside_stock,
    `Packing.Polygons.arc_point_in_hull, `Packing.Orthogonal.intervals_match_crossings,
    `Packing.Orthogonal.cleared_material_disjoint, `Packing.Sloped.separation_between,
    `Packing.Sloped.strip_material_matches_crossings, `Packing.Sloped.fitting_tile_inside_stock,
    `Packing.Sloped.cleared_shapes_disjoint,
    `Packing.Optimality.checkOptimalLinear_sound, `Packing.Optimality.checkOptimalRectangular_sound,
    `Packing.Optimality.checkCostBound_sound, `Packing.ExactLinear.attainable_iff,
    `Packing.ExactLinear.excludes_better_plan, `Packing.ExactGrid.check_sound,
    `Packing.Bounds.floor_preserves_chain, `Packing.Bounds.threshold_preserves_chain,
    `Packing.Bounds.transformed_layout_fits_2d, `Packing.Bounds.transformed_layout_fits_3d,
    `Packing.Bounds.lower_bound_2d_sound, `Packing.Bounds.lower_bound_3d_sound,
    `Packing.Bounds.checkLowerBound2D_sound,
    `Packing.Optimization.rank_irrefl, `Packing.Optimization.rank_trans,
    `Packing.Optimization.exactKnapsack1D_sound, `Packing.Optimization.exactKnapsackGrid_sound,
    `Packing.Optimization.exactCostGrid_sound, `Packing.Optimization.exactOpenDim_sound,
    `Packing.Optimization.infeasible1D_sound, `Packing.Optimization.infeasibleGrid_sound,
    `Packing.Reuse.offcuts_disjoint_from_parts_and_each_other,
    `Packing.Reuse.future_placements_valid_and_disjoint, `Packing.Reuse.fulfilled_accounting_sound,
    `Packing.CutPlan.replayBar_preserves_length_and_counts,
    `Packing.CutPlan.cncState_balanced_and_bounded,
    `Packing.IrregularExact.exact_rotation_preserves_distance,
    `Packing.IrregularExact.general_rotation_error_bound,
    `Packing.IrregularExact.inflated_clearance_certifies_exact,
    `Packing.IrregularExact.tileFitsWithGap_sound, `Packing.IrregularExact.tilesClearWithGap_sound,
    `Packing.IrregularExact.circle_clears_segment, `Packing.IrregularExact.arc_sagitta_bound,
    `Packing.IrregularExact.arc_in_chord_slab,
    `Packing.Semantics.accounting_sound, `Packing.Semantics.checkGroups_sound,
    `Packing.Semantics.checkStages_sound, `Packing.Semantics.saw_schedule_conserves_area,
    `Packing.Semantics.saw_cut_preserves_parts, `Packing.Semantics.checkWeightsAbove_iff,
    `Packing.Semantics.density_sound, `Packing.Semantics.unloading_unblocked,
    `Packing.Semantics.bounded_search_terminates_and_respects_budget,
    `Packing.Semantics.checkValidInput_iff]
  for theoremName in guarantees do
    for assumption in ← Lean.collectAxioms theoremName do
      unless standard.contains assumption do
        throwError "unexpected axiom {assumption} in {theoremName}"

def checkCertificate (entry : Json) : Except String Bool := do
  let tag ← entry.getObjValAs? String "dimension"
  let problem ← entry.getObjVal? "problem"
  let solution ← entry.getObjVal? "solution"
  match tag with
  | "staged_2d" => Staged.checkStaged problem solution
  | "saw_plan" => Saw.checkSaw problem solution
  | "loading_3d" => Loading.checkLoading problem solution
  | "irregular_circles" => Circles.checkCirclePacking problem solution
  | "irregular_polygons" => Polygons.checkPolygonPacking problem solution
  | "irregular_envelopes" => Polygons.checkEnvelopePacking problem solution
  | "irregular_orthogonal" => Orthogonal.checkOrthogonalPacking problem solution
  | "irregular_sloped" => Sloped.checkSlopedPacking problem solution
  | "irregular_sloped_cleared" => IrregularExact.checkSlopedClearedPacking problem solution
  | "irregular_curved_exact" => IrregularExact.checkCurvedExactPacking problem solution
  | "optimal_1d" => Optimality.checkOptimalLinearOutput problem solution
  | "min_cost_1d" => Optimality.checkMinimumLinearCost problem solution
  | "exact_1d" => ExactLinear.checkOutput .count problem solution
  | "exact_min_cost_1d" => ExactLinear.checkOutput .cost problem solution
  | "optimal_2d" => Optimality.checkOptimalRectangularOutput .sheet problem solution
  | "optimal_3d" => Optimality.checkOptimalRectangularOutput .box problem solution
  | "exact_count_2d" => ExactGrid.checkOutput .sheet problem solution
  | "exact_count_3d" => ExactGrid.checkOutput .box problem solution
  | "lower_bound_2d" => Bounds.checkLowerBound2D problem solution
  | "lower_bound_3d" => Bounds.checkLowerBound3D problem solution
  | "optimized_1d" => Optimization.checkOptimized1D problem solution
  | "optimized_2d" => Optimization.checkOptimized2D problem solution
  | "optimized_3d" => Optimization.checkOptimized3D problem solution
  | "optimized_staged_2d" => Optimization.checkOptimizedStaged2D problem solution
  | "optimized_loading_3d" => Optimization.checkOptimizedLoading3D problem solution
  | "exact_knapsack_1d" => Optimization.checkExactKnapsackOutput .linear problem solution
  | "exact_knapsack_2d" => Optimization.checkExactKnapsackOutput .sheet problem solution
  | "exact_knapsack_3d" => Optimization.checkExactKnapsackOutput .box problem solution
  | "exact_cost_2d" => Optimization.checkExactCostGridOutput .sheet problem solution
  | "exact_cost_3d" => Optimization.checkExactCostGridOutput .box problem solution
  | "exact_open_1d" => Optimization.checkExactOpenDimOutput .linear problem solution
  | "exact_open_2d" => Optimization.checkExactOpenDimOutput .sheet problem solution
  | "exact_open_3d" => Optimization.checkExactOpenDimOutput .box problem solution
  | "infeasible_1d" => Optimization.checkInfeasibleOutput .linear problem solution
  | "infeasible_2d" => Optimization.checkInfeasibleOutput .sheet problem solution
  | "infeasible_3d" => Optimization.checkInfeasibleOutput .box problem solution
  | "reuse_eval_2d" => Reuse.checkReuseEvaluation problem solution
  | "reuse_solve_2d" => Reuse.checkReuseSolution problem solution
  | "cut_plan_1d" => CutPlan.checkCutPlan1D problem solution
  | "cut_plan_2d" => CutPlan.checkCutPlan2D problem solution
  | "accounting_1d" => Semantics.checkAccounting1D problem solution
  | "accounting_2d" => Semantics.checkAccounting2D problem solution
  | "accounting_3d" => Semantics.checkAccounting3D problem solution
  | "constrained_2d" => Indexed.checkConstrained .sheet problem solution
  | "constrained_3d" => Indexed.checkConstrained .box problem solution
  | _ =>
    let dim ← dimension tag
    return (← readCertificate dim problem solution).check

def runCase (entry : Json) : Except String Unit := do
  let label ← entry.getObjValAs? String "label"
  let expected ← entry.getObjValAs? Bool "accepted"
  let rejection := (entry.getObjValAs? String "rejection").toOption
  match checkCertificate entry with
  | .ok accepted =>
    unless accepted == expected && rejection.isNone do
      throw s!"{label}: expected acceptance = {expected}, got {accepted}"
  | .error reason =>
    unless !expected && rejection == some reason do throw s!"{label}: {reason}"

def main (args : List String) : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let json ← IO.ofExcept (Json.parse input)
  match args with
  | ["--verify"] =>
    unless ← IO.ofExcept (checkCertificate json) do
      throw (IO.userError "packing certificate failed verification")
    IO.println "Lean accepted packing certificate"
  | [] =>
    let cases ← IO.ofExcept (fromJson? (α := List Json) json)
    if cases.isEmpty then throw (IO.userError "no packing certificates supplied")
    for entry in cases do
      IO.ofExcept (runCase entry)
    IO.println s!"Lean checked {cases.length} packing certificate cases"
  | _ => throw (IO.userError "expected --verify or no arguments")
