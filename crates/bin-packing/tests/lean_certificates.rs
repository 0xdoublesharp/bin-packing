//! End-to-end fixtures for the optional Lean certificate checker.

use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use bin_packing::BinPackingError;
use bin_packing::cut_plan::CutPlanError;
use bin_packing::irregular::{
    Contour2D, CurveSegment2D, IrregularBin, IrregularDemand, IrregularOptions, IrregularProblem,
    Point2D, Polygon2D, RotationRange2D, Shape2D, solve_irregular, validate_irregular,
};
use bin_packing::one_d::cut_plan::{self as bar_plan, CutPlanOptions1D, CutStep1D};
use bin_packing::one_d::optimization::{OptimizationOptions, PackingObjective, solve_1d_optimized};
use bin_packing::one_d::{
    CutDemand1D, OneDAlgorithm, OneDOptions, OneDProblem, Stock1D, solve_1d, solve_1d_arc_flow,
    solve_1d_min_cost,
};
use bin_packing::optimization::OptimizationProblem;
use bin_packing::three_d::constrained::{
    ConstrainedOptions3D, ConstrainedProblem3D, solve_3d_constrained,
};
use bin_packing::three_d::loading::{
    AxleLimits3D, AxleLoads3D, FloorAxis3D, LoadingBinRules3D, LoadingOptions3D, LoadingProblem3D,
    StackItemRules3D, UnloadingConstraint3D, WeightDensity3D, solve_loading_3d,
};
use bin_packing::three_d::optimization::{solve_3d_optimized, solve_loading_3d_optimized};
use bin_packing::three_d::{
    Bin3D, BoxDemand3D, RotationMask3D, ThreeDAlgorithm, ThreeDOptions, ThreeDProblem, solve_3d,
    solve_3d_repaired,
};
use bin_packing::two_d::adaptive::{AdaptiveOptions2D, solve_2d_adaptive};
use bin_packing::two_d::constrained::{
    ConstrainedOptions2D, ConstrainedProblem2D, Defect2D, SheetConstraints2D, solve_2d_constrained,
};
use bin_packing::two_d::cut_plan::{
    self as sheet_plan, CutPlanOptions2D, CutPlanPreset2D, CutStep2D,
};
use bin_packing::two_d::optimization::{solve_2d_optimized, solve_2d_staged_optimized};
use bin_packing::two_d::reuse::{
    ForecastPart2D, ReuseError2D, ReuseForecast2D, ReuseOptions2D, evaluate_reuse,
    solve_2d_with_reuse,
};
use bin_packing::two_d::saw_plan::{
    SawAction2D, SawJob2D, SawLayout2D, SawMachine2D, SawPlanOptions2D, SawRect2D,
    SawSearchLimits2D, plan_saw_cuts,
};
use bin_packing::two_d::staged::{
    StagedCutType2D, StagedOptions2D, StagedProblem2D, StagedRules2D, solve_2d_staged,
};
use bin_packing::two_d::{
    Placement2D, RectDemand2D, Sheet2D, TwoDAlgorithm, TwoDOptions, TwoDProblem, lower_bound_2d,
    solve_2d, solve_2d_demand_aware, solve_2d_mixed_rotations, solve_2d_recombined,
};
use serde::Serialize;
use serde_json::{Value, json};

fn certificate(
    dimension: &str,
    label: impl Into<String>,
    problem: &impl Serialize,
    solution: &impl Serialize,
) -> Value {
    json!({
        "dimension": dimension,
        "label": label.into(),
        "problem": problem,
        "solution": solution,
        "accepted": true,
    })
}

fn reject(cases: &mut Vec<Value>, source: &Value, label: &str, mutate: impl FnOnce(&mut Value)) {
    let mut forged = source.clone();
    forged["label"] = json!(label);
    forged["accepted"] = json!(false);
    mutate(&mut forged);
    cases.push(forged);
}

fn linear_cases(cases: &mut Vec<Value>) {
    let mut problem = OneDProblem {
        stock: vec![Stock1D {
            name: "bar".into(),
            length: 11,
            kerf: 2,
            trim: 1,
            cost: 1.0,
            available: None,
        }],
        demands: vec![CutDemand1D { name: "rail".into(), length: 4, quantity: 3 }],
    };
    for algorithm in [
        OneDAlgorithm::Auto,
        OneDAlgorithm::FirstFitDecreasing,
        OneDAlgorithm::BestFitDecreasing,
        OneDAlgorithm::LocalSearch,
        OneDAlgorithm::ColumnGeneration,
    ] {
        let options = OneDOptions { algorithm, seed: Some(42), ..OneDOptions::default() };
        let solution = solve_1d(problem.clone(), options).expect("linear fixture should solve");
        assert!(solution.unplaced.is_empty(), "{algorithm:?} dropped a rail");
        cases.push(certificate("1d", format!("1D {algorithm:?}"), &problem, &solution));
        if algorithm == OneDAlgorithm::ColumnGeneration {
            let optimal = certificate("optimal_1d", "1D minimum stock count", &problem, &solution);
            let mut extra_stock = optimal.clone();
            let layouts: Vec<_> = solution
                .layouts
                .iter()
                .flat_map(|layout| {
                    layout.cuts.iter().map(|cut| {
                        json!({
                            "stock_name": layout.stock_name,
                            "stock_length": layout.stock_length,
                            "cuts": [cut],
                            "used_length": 4,
                            "remaining_length": 6,
                            "waste": 6,
                        })
                    })
                })
                .collect();
            extra_stock["solution"]["layouts"] = json!(layouts);
            extra_stock["solution"]["stock_count"] = json!(layouts.len());
            reject(cases, &extra_stock, "1D feasible solution fails optimality witness", |_| {});
            extra_stock["dimension"] = json!("1d");
            extra_stock["label"] = json!("1D same extra-stock witness passes feasibility");
            cases.push(extra_stock);
            cases.push(optimal);
        }
    }
    let options = OneDOptions::default();
    let count = solve_1d_arc_flow(problem.clone(), options.clone()).expect("arc-flow fixture");
    let cost = solve_1d_min_cost(problem.clone(), options).expect("minimum-cost fixture");
    assert!(count.unplaced.is_empty());
    assert!(cost.unplaced.is_empty());
    cases.push(certificate("optimal_1d", "1D arc-flow stock-count witness", &problem, &count));
    cases.push(certificate("optimal_1d", "1D single-price minimum-cost layout", &problem, &cost));

    problem.stock[0].available = Some(1);
    let solution =
        solve_1d(problem.clone(), OneDOptions::default()).expect("capped stock can solve");
    assert_eq!(solution.layouts[0].cuts.len(), 2);
    assert_eq!(solution.unplaced.len(), 1);
    let valid = certificate("1d", "1D trim, kerf, and stock shortage", &problem, &solution);
    reject(cases, &valid, "1D reported usage omits the saw gap", |case| {
        let layout = &mut case["solution"]["layouts"][0];
        layout["used_length"] = json!(8);
        layout["remaining_length"] = json!(2);
        layout["waste"] = json!(2);
    });
    reject(cases, &valid, "1D material cannot reach the final cut after trim", |case| {
        case["problem"]["stock"][0]["trim"] = json!(2);
        case["solution"]["layouts"][0]["used_length"] = json!(9);
    });
    reject(cases, &valid, "1D stock cap exceeded with demand conserved", |case| {
        let layout = case["solution"]["layouts"][0].clone();
        case["solution"]["layouts"].as_array_mut().expect("layout list").push(layout);
        case["solution"]["stock_count"] = json!(2);
        case["problem"]["demands"][0]["quantity"] = json!(5);
    });
    reject(cases, &valid, "1D dropped shortage", |case| {
        case["solution"]["unplaced"] = json!([]);
    });
    cases.push(valid);

    problem.stock.push(Stock1D {
        name: "short bar".into(),
        length: 4,
        kerf: 0,
        trim: 0,
        cost: 1.0,
        available: Some(1),
    });
    problem.demands.push(CutDemand1D { name: "brace".into(), length: 4, quantity: 2 });
    let solution =
        solve_1d(problem.clone(), OneDOptions::default()).expect("mixed stock can solve");
    assert_eq!(solution.layouts.len(), 2);
    assert_eq!(solution.unplaced.len(), 2);
    let valid =
        certificate("1d", "1D mixed stock and equal-length demand types", &problem, &solution);
    let other_demand = if solution.unplaced[0].name == "rail" { "brace" } else { "rail" };
    reject(cases, &valid, "1D per-demand shortage is wrong despite equal totals", |case| {
        case["solution"]["unplaced"][0]["name"] = json!(other_demand);
    });
    reject(cases, &valid, "1D forged stock length", |case| {
        case["solution"]["layouts"][0]["stock_length"] = json!(12);
    });
    cases.push(valid);

    let problem = OneDProblem {
        stock: vec![
            Stock1D {
                name: "long".into(),
                length: 12,
                kerf: 0,
                trim: 0,
                cost: 14.0,
                available: Some(1),
            },
            Stock1D {
                name: "short".into(),
                length: 6,
                kerf: 0,
                trim: 0,
                cost: 6.0,
                available: Some(2),
            },
        ],
        demands: vec![CutDemand1D { name: "rail".into(), length: 6, quantity: 2 }],
    };
    let cheap = solve_1d_min_cost(problem.clone(), OneDOptions::default())
        .expect("two short bars cost less");
    assert_eq!(cheap.stock_count, 2);
    assert_eq!(cheap.total_cost, 12.0);
    let valid = certificate("min_cost_1d", "1D exact multi-stock cost bound", &problem, &cheap);
    reject(cases, &valid, "1D forged total cost below actual stock charge", |case| {
        case["solution"]["total_cost"] = json!(11.0);
    });
    cases.push(valid);

    let fewer = solve_1d(problem.clone(), OneDOptions::default()).expect("one long bar fits");
    assert_eq!(fewer.stock_count, 1);
    assert_eq!(fewer.total_cost, 14.0);
    let mut costly = certificate("min_cost_1d", "1D fewer bars with higher cost", &problem, &fewer);
    costly["accepted"] = json!(false);
    cases.push(costly);

    cases.push(certificate(
        "exact_1d",
        "1D count-first prefers one expensive bar",
        &problem,
        &fewer,
    ));
    cases.push(certificate(
        "exact_min_cost_1d",
        "1D cost-first prefers two cheap bars",
        &problem,
        &cheap,
    ));
    let mut wrong_objective = certificate(
        "exact_1d",
        "1D cost optimum loses under count-first ranking",
        &problem,
        &cheap,
    );
    wrong_objective["accepted"] = json!(false);
    cases.push(wrong_objective);
    let mut wrong_objective = certificate(
        "exact_min_cost_1d",
        "1D count optimum loses under cost-first ranking",
        &problem,
        &fewer,
    );
    wrong_objective["accepted"] = json!(false);
    cases.push(wrong_objective);

    let mut free_stock = problem.clone();
    free_stock.stock[0].cost = 0.0;
    free_stock.stock[1].cost = -0.0;
    let free = solve_1d_min_cost(free_stock.clone(), OneDOptions::default())
        .expect("zero prices use the bar-count tie-breaker");
    assert_eq!(free.stock_count, 1, "signed zero prices must compare equally");
    cases.push(certificate(
        "exact_min_cost_1d",
        "1D positive and negative zero prices are equal",
        &free_stock,
        &free,
    ));

    let mut problem = OneDProblem {
        stock: vec![
            Stock1D {
                name: "wide".into(),
                length: 14,
                kerf: 2,
                trim: 1,
                cost: 8.0,
                available: Some(1),
            },
            Stock1D {
                name: "narrow".into(),
                length: 8,
                kerf: 0,
                trim: 1,
                cost: 7.0,
                available: Some(2),
            },
        ],
        demands: vec![CutDemand1D { name: "rail".into(), length: 6, quantity: 2 }],
    };
    let solution = solve_1d_min_cost(problem.clone(), OneDOptions::default())
        .expect("trim and kerf force two bars");
    assert!(solution.exact);
    assert_eq!(solution.total_cost, 14.0);
    let exact = certificate(
        "exact_min_cost_1d",
        "1D exact cost despite inconclusive usable-length bound",
        &problem,
        &solution,
    );
    reject(cases, &exact, "1D price bound is too weak on the same optimum", |case| {
        case["dimension"] = json!("min_cost_1d");
    });
    reject(cases, &exact, "1D exact search validates reported waste", |case| {
        case["solution"]["total_waste"] = json!(0);
    });
    cases.push(exact);

    problem.stock[1].available = Some(1);
    problem.demands[0].quantity = 3;
    let partial = solve_1d_arc_flow(problem.clone(), OneDOptions::default())
        .expect("inventory forces a shortage");
    assert!(partial.exact);
    assert_eq!(partial.unplaced.len(), 1);
    let exact = certificate("exact_1d", "1D partial fulfillment is optimal", &problem, &partial);
    reject(cases, &exact, "1D better fulfillment becomes possible with more stock", |case| {
        case["problem"]["stock"][1]["available"] = json!(2);
    });
    cases.push(exact);

    problem.stock[1].available = None;
    problem.demands[0].quantity = 8;
    let larger = solve_1d_arc_flow(problem.clone(), OneDOptions::default())
        .expect("larger exact solver fixture");
    assert!(larger.exact);
    cases.push(certificate("1d", "1D feasible above exact proof budget", &problem, &larger));
    let mut over_budget =
        certificate("exact_1d", "1D exact checker fails closed over budget", &problem, &larger);
    over_budget["accepted"] = json!(false);
    cases.push(over_budget);
}

fn sheet_cases(cases: &mut Vec<Value>) {
    let problem = TwoDProblem {
        sheets: vec![Sheet2D {
            name: "sheet".into(),
            width: 48,
            height: 10,
            cost: 1.0,
            quantity: Some(1),
            kerf: 1,
            edge_kerf_relief: true,
        }],
        demands: vec![RectDemand2D {
            name: "panel".into(),
            width: 24,
            height: 10,
            quantity: 3,
            can_rotate: false,
        }],
    };
    for algorithm in [
        TwoDAlgorithm::Auto,
        TwoDAlgorithm::MaxRects,
        TwoDAlgorithm::MaxRectsBestShortSideFit,
        TwoDAlgorithm::MaxRectsBestLongSideFit,
        TwoDAlgorithm::MaxRectsBottomLeft,
        TwoDAlgorithm::MaxRectsContactPoint,
        TwoDAlgorithm::Skyline,
        TwoDAlgorithm::SkylineMinWaste,
        TwoDAlgorithm::Guillotine,
        TwoDAlgorithm::GuillotineBestShortSideFit,
        TwoDAlgorithm::GuillotineBestLongSideFit,
        TwoDAlgorithm::GuillotineShorterLeftoverAxis,
        TwoDAlgorithm::GuillotineLongerLeftoverAxis,
        TwoDAlgorithm::GuillotineMinAreaSplit,
        TwoDAlgorithm::GuillotineMaxAreaSplit,
        TwoDAlgorithm::NextFitDecreasingHeight,
        TwoDAlgorithm::FirstFitDecreasingHeight,
        TwoDAlgorithm::BestFitDecreasingHeight,
        TwoDAlgorithm::MultiStart,
        TwoDAlgorithm::RotationSearch,
    ] {
        let options = TwoDOptions { algorithm, seed: Some(42), ..TwoDOptions::default() };
        let solution = solve_2d(problem.clone(), options).expect("sheet fixture should solve");
        assert_eq!(solution.layouts[0].placements.len(), 2, "{algorithm:?} missed edge relief");
        assert_eq!(solution.unplaced[0].quantity, 1, "{algorithm:?} missed the shortage");
        cases.push(certificate("2d", format!("2D {algorithm:?}"), &problem, &solution));
    }

    let solution =
        solve_2d(problem.clone(), TwoDOptions::default()).expect("edge relief can solve");
    let valid = certificate("2d", "2D edge relief source", &problem, &solution);
    reject(cases, &valid, "2D forbidden edge overrun", |case| {
        case["problem"]["sheets"][0]["edge_kerf_relief"] = json!(false);
    });
    reject(cases, &valid, "2D touching panels violate positive kerf", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[0]["x"] = json!(0);
        placements[1]["x"] = json!(24);
    });
    reject(cases, &valid, "2D overlapping panels", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[0]["x"] = json!(0);
        placements[1]["x"] = json!(23);
    });
    reject(cases, &valid, "2D forged unplaced identity", |case| {
        case["solution"]["unplaced"][0]["name"] = json!("unknown panel");
    });
    reject(cases, &valid, "2D forged layout count", |case| {
        case["solution"]["sheet_count"] = json!(2);
    });
    reject(cases, &valid, "2D unknown stock identity", |case| {
        case["solution"]["layouts"][0]["sheet_name"] = json!("unknown sheet");
    });

    let mut tiled = problem.clone();
    tiled.sheets[0].quantity = None;
    tiled.demands[0].quantity = 5;
    let solution = solve_2d(tiled.clone(), TwoDOptions::default()).expect("uncapped sheet tiling");
    assert_eq!(solution.sheet_count, 3);
    assert!(solution.unplaced.is_empty());
    cases.push(certificate("optimal_2d", "2D minimum sheet count", &tiled, &solution));

    let mut rotated = problem;
    rotated.demands[0] = RectDemand2D {
        width: 10,
        height: 24,
        quantity: 1,
        can_rotate: true,
        name: "rotated panel".into(),
    };
    let solution =
        solve_2d(rotated.clone(), TwoDOptions::default()).expect("quarter turn should fit");
    assert!(solution.layouts[0].placements[0].rotated);
    let valid = certificate("2d", "2D forced quarter turn", &rotated, &solution);
    reject(cases, &valid, "2D forbidden quarter turn", |case| {
        case["problem"]["demands"][0]["can_rotate"] = json!(false);
    });
    cases.push(valid);

    let square = Sheet2D {
        name: "square".into(),
        width: 5,
        height: 5,
        cost: 1.0,
        quantity: None,
        kerf: 0,
        edge_kerf_relief: false,
    };
    let problem = TwoDProblem {
        sheets: vec![square.clone()],
        demands: vec![RectDemand2D {
            name: "tile".into(),
            width: 3,
            height: 3,
            quantity: 2,
            can_rotate: false,
        }],
    };
    let solution =
        solve_2d(problem.clone(), TwoDOptions::default()).expect("two tiles need two sheets");
    assert_eq!(solution.sheet_count, 2);
    assert!(solution.unplaced.is_empty());
    let exact = certificate(
        "exact_count_2d",
        "2D exact count despite a loose area bound",
        &problem,
        &solution,
    );
    reject(cases, &exact, "2D area alone cannot certify this result", |case| {
        case["dimension"] = json!("optimal_2d");
    });
    let mut mixed = problem;
    mixed.sheets.push(Sheet2D { name: "wide".into(), width: 6, quantity: Some(0), ..square });
    let capped = certificate(
        "exact_count_2d",
        "2D cheaper layout requires unavailable stock",
        &mixed,
        &solution,
    );
    reject(cases, &capped, "2D wider sheet makes the same feasible result suboptimal", |case| {
        case["problem"]["sheets"][1]["quantity"] = json!(1);
    });
    cases.extend([exact, capped]);
}

fn box_cases(cases: &mut Vec<Value>) {
    let mut problem = ThreeDProblem {
        bins: vec![Bin3D {
            name: "crate".into(),
            width: 6,
            height: 5,
            depth: 4,
            cost: 1.0,
            quantity: Some(1),
        }],
        demands: vec![BoxDemand3D {
            name: "box".into(),
            width: 2,
            height: 4,
            depth: 5,
            quantity: 4,
            allowed_rotations: RotationMask3D::XZY,
        }],
    };
    for algorithm in [
        ThreeDAlgorithm::Auto,
        ThreeDAlgorithm::ExtremePoints,
        ThreeDAlgorithm::ExtremePointsResidualSpace,
        ThreeDAlgorithm::ExtremePointsFreeVolume,
        ThreeDAlgorithm::ExtremePointsBottomLeftBack,
        ThreeDAlgorithm::ExtremePointsContactPoint,
        ThreeDAlgorithm::ExtremePointsEuclidean,
        ThreeDAlgorithm::Guillotine3D,
        ThreeDAlgorithm::Guillotine3DBestShortSideFit,
        ThreeDAlgorithm::Guillotine3DBestLongSideFit,
        ThreeDAlgorithm::Guillotine3DShorterLeftoverAxis,
        ThreeDAlgorithm::Guillotine3DLongerLeftoverAxis,
        ThreeDAlgorithm::Guillotine3DMinVolumeSplit,
        ThreeDAlgorithm::Guillotine3DMaxVolumeSplit,
        ThreeDAlgorithm::LayerBuilding,
        ThreeDAlgorithm::LayerBuildingMaxRects,
        ThreeDAlgorithm::LayerBuildingSkyline,
        ThreeDAlgorithm::LayerBuildingGuillotine,
        ThreeDAlgorithm::LayerBuildingShelf,
        ThreeDAlgorithm::WallBuilding,
        ThreeDAlgorithm::ColumnBuilding,
        ThreeDAlgorithm::DeepestBottomLeft,
        ThreeDAlgorithm::DeepestBottomLeftFill,
        ThreeDAlgorithm::FirstFitDecreasingVolume,
        ThreeDAlgorithm::BestFitDecreasingVolume,
        ThreeDAlgorithm::MultiStart,
        ThreeDAlgorithm::Grasp,
        ThreeDAlgorithm::LocalSearch,
    ] {
        let options = ThreeDOptions { algorithm, seed: Some(42), ..ThreeDOptions::default() };
        let solution = solve_3d(problem.clone(), options).expect("box fixture should solve");
        assert!(!solution.layouts[0].placements.is_empty(), "{algorithm:?} placed no boxes");
        assert!(!solution.unplaced.is_empty(), "{algorithm:?} exceeded physical capacity");
        cases.push(certificate("3d", format!("3D {algorithm:?}"), &problem, &solution));
    }
    let solution = solve_3d(problem.clone(), ThreeDOptions::default()).expect("box rotation fits");
    let valid = certificate("3d", "3D restricted orientation source", &problem, &solution);
    reject(cases, &valid, "3D forbidden orientation", |case| {
        case["problem"]["demands"][0]["allowed_rotations"] = json!(1);
    });
    reject(cases, &valid, "3D overlap from duplicated coordinates", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[1] = placements[0].clone();
    });
    reject(cases, &valid, "3D depth outside the bin", |case| {
        case["solution"]["layouts"][0]["placements"][0]["z"] = json!(u32::MAX);
    });

    // Branch-and-bound requires a single uncapped stock and identity-only demands.
    problem.bins[0].quantity = None;
    problem.demands[0].height = 5;
    problem.demands[0].depth = 4;
    problem.demands[0].allowed_rotations = RotationMask3D::XYZ;
    let options =
        ThreeDOptions { algorithm: ThreeDAlgorithm::BranchAndBound, ..ThreeDOptions::default() };
    let solution = solve_3d(problem.clone(), options).expect("restricted exact fixture can solve");
    assert!(solution.unplaced.is_empty());
    cases.push(certificate("3d", "3D BranchAndBound", &problem, &solution));
    cases.push(certificate("optimal_3d", "3D minimum bin count", &problem, &solution));

    problem.bins[0].width = 5;
    problem.bins[0].depth = 5;
    problem.demands[0].width = 3;
    problem.demands[0].height = 3;
    problem.demands[0].depth = 3;
    problem.demands[0].quantity = 2;
    let solution =
        solve_3d(problem.clone(), ThreeDOptions::default()).expect("two cubes need two bins");
    assert_eq!(solution.bin_count, 2);
    assert!(solution.unplaced.is_empty());
    let exact = certificate(
        "exact_count_3d",
        "3D exact count despite a loose volume bound",
        &problem,
        &solution,
    );
    reject(cases, &exact, "3D volume alone cannot certify this result", |case| {
        case["dimension"] = json!("optimal_3d");
    });
    reject(cases, &exact, "3D longer bins make a one-bin packing possible", |case| {
        case["problem"]["bins"][0]["depth"] = json!(6);
        for layout in case["solution"]["layouts"].as_array_mut().expect("layout array") {
            layout["depth"] = json!(6);
        }
    });
    cases.push(exact);
}

fn constrained_cases(cases: &mut Vec<Value>) {
    let problem = ConstrainedProblem2D {
        problem: TwoDProblem {
            sheets: vec![Sheet2D {
                name: "trimmed".into(),
                width: 12,
                height: 8,
                cost: 1.0,
                quantity: Some(1),
                kerf: 1,
                edge_kerf_relief: false,
            }],
            demands: [4, 3]
                .into_iter()
                .map(|width| RectDemand2D {
                    name: "reused label".into(),
                    width,
                    height: 6,
                    quantity: 1,
                    can_rotate: false,
                })
                .collect(),
        },
        constraints: vec![SheetConstraints2D {
            trim_top: 1,
            trim_bottom: 1,
            trim_right: 1,
            trim_left: 1,
            defects: vec![Defect2D { x: 6, y: 1, width: 1, height: 6 }],
        }],
    };
    let solution = solve_2d_constrained(problem.clone(), ConstrainedOptions2D::default())
        .expect("constrained sheet fixture should solve");
    assert_eq!(solution.solution.layouts[0].placements.len(), 2);
    assert!(solution.solution.unplaced.is_empty());
    let valid = certificate(
        "constrained_2d",
        "2D trimmed sheet, defect and duplicate labels",
        &problem,
        &solution,
    );
    reject(cases, &valid, "2D constrained defect violates blade clearance", |case| {
        case["problem"]["constraints"][0]["defects"][0]["x"] = json!(5);
    });
    reject(cases, &valid, "2D constrained part enters top trim", |case| {
        case["problem"]["constraints"][0]["trim_top"] = json!(2);
    });
    reject(cases, &valid, "2D constrained swaps equal labels across source indices", |case| {
        case["solution"]["demand_indices"][0].as_array_mut().expect("indices").swap(0, 1);
    });
    cases.push(valid);

    let problem = ConstrainedProblem3D {
        problem: ThreeDProblem {
            bins: vec![Bin3D {
                name: "payload restricted".into(),
                width: 7,
                height: 3,
                depth: 3,
                cost: 1.0,
                quantity: Some(1),
            }],
            demands: [1, 2]
                .into_iter()
                .map(|quantity| BoxDemand3D {
                    name: "same shell".into(),
                    width: 2,
                    height: 3,
                    depth: 3,
                    quantity,
                    allowed_rotations: RotationMask3D::XYZ,
                })
                .collect(),
        },
        item_weights: vec![4, 6],
        bin_max_weights: vec![Some(10)],
    };
    let solution = solve_3d_constrained(problem.clone(), ConstrainedOptions3D::default())
        .expect("constrained bin fixture should solve");
    assert_eq!(solution.bin_weights, [10]);
    assert_eq!(solution.solution.unplaced.len(), 1);
    let valid = certificate(
        "constrained_3d",
        "3D indexed payload with duplicate labels",
        &problem,
        &solution,
    );
    reject(cases, &valid, "3D constrained actual payload exceeds cap", |case| {
        case["problem"]["bin_max_weights"][0] = json!(9);
    });
    reject(cases, &valid, "3D constrained forged payload total", |case| {
        case["solution"]["bin_weights"][0] = json!(9);
    });
    cases.push(valid);
}

fn staged_cases(cases: &mut Vec<Value>) {
    let mut problem = StagedProblem2D {
        packing: ConstrainedProblem2D {
            problem: TwoDProblem {
                sheets: vec![Sheet2D {
                    name: "board".into(),
                    width: 13,
                    height: 6,
                    cost: 1.0,
                    quantity: Some(1),
                    kerf: 1,
                    edge_kerf_relief: false,
                }],
                demands: vec![
                    RectDemand2D {
                        name: "strip".into(),
                        width: 5,
                        height: 4,
                        quantity: 1,
                        can_rotate: false,
                    };
                    2
                ],
            },
            constraints: vec![SheetConstraints2D {
                trim_top: 1,
                trim_bottom: 1,
                trim_right: 1,
                trim_left: 1,
                ..SheetConstraints2D::default()
            }],
        },
        rules: StagedRules2D {
            max_stages: Some(1),
            cut_type: StagedCutType2D::Exact,
            maximum_number_1_cuts: Some(1),
            minimum_distance_1_cuts: 5,
            ..StagedRules2D::default()
        },
        groups: vec![Some(7), Some(7)],
    };
    let solution = solve_2d_staged(problem.clone(), StagedOptions2D::default())
        .expect("staged cut with trims and kerf should solve");
    assert_eq!(solution.trees[0].nodes.len(), 3);
    assert_eq!(solution.production_order.len(), 2);
    assert_eq!(solution.solution.total_kerf_area, 4);
    let valid = certificate(
        "staged_2d",
        "staged exact guillotine cut with trims and kerf",
        &problem,
        &solution,
    );
    reject(cases, &valid, "staged wrong reconstructed child bounds", |case| {
        case["solution"]["trees"][0]["nodes"][1]["region"]["x"] = json!(2);
    });
    reject(cases, &valid, "staged kerf area altered", |case| {
        case["solution"]["solution"]["total_kerf_area"] = json!(0);
    });
    reject(cases, &valid, "staged omitted production entry", |case| {
        case["solution"]["production_order"].as_array_mut().expect("production list").truncate(1);
    });
    reject(cases, &valid, "staged productive strip too narrow", |case| {
        case["problem"]["rules"]["minimum_distance_1_cuts"] = json!(6);
    });
    reject(cases, &valid, "staged cutting count exceeded", |case| {
        case["problem"]["rules"]["maximum_number_1_cuts"] = json!(0);
    });
    reject(cases, &valid, "staged finishing priority inverted", |case| {
        let node_indices: Vec<_> = case["solution"]["production_order"]
            .as_array()
            .expect("production order")
            .iter()
            .map(|p| usize::try_from(p["node_index"].as_u64().expect("number")).expect("index"))
            .collect();
        case["solution"]["trees"][0]["nodes"][node_indices[0]]["action"]["demand_index"] = json!(1);
        case["solution"]["trees"][0]["nodes"][node_indices[1]]["action"]["demand_index"] = json!(0);
        case["solution"]["demand_indices"][0] = json!([1, 0]);
    });
    reject(cases, &valid, "staged reused child index", |case| {
        let children = &mut case["solution"]["trees"][0]["nodes"][0]["action"]["children"];
        children[1] = children[0].clone();
        case["rejection"] = json!("cut tree reuses a node");
    });
    cases.push(valid);

    let stock = &mut problem.packing.problem.sheets[0];
    stock.width = 10;
    stock.height = 10;
    stock.kerf = 0;
    problem.packing.problem.demands.truncate(1);
    problem.packing.problem.demands[0].quantity = 2;
    problem.groups.clear();
    problem.packing.constraints = vec![SheetConstraints2D {
        defects: vec![Defect2D { x: 4, y: 8, width: 2, height: 1 }],
        ..SheetConstraints2D::default()
    }];
    problem.rules = StagedRules2D {
        max_stages: Some(2),
        cut_type: StagedCutType2D::Exact,
        cut_through_defects: true,
        ..StagedRules2D::default()
    };
    let options = StagedOptions2D { max_states: 0, ..StagedOptions2D::default() };
    let solution = solve_2d_staged(problem.clone(), options).expect("allowed defect crossing");
    assert!(solution.solution.unplaced.is_empty());
    let valid = certificate(
        "staged_2d",
        "staged explicitly allowed zero-width blade crossing",
        &problem,
        &solution,
    );
    reject(cases, &valid, "staged zero-width blade crosses protected defect", |case| {
        case["problem"]["rules"]["cut_through_defects"] = json!(false);
    });
    cases.push(valid);
}

fn loading_cases(cases: &mut Vec<Value>) {
    let mut problem = LoadingProblem3D {
        packing: ConstrainedProblem3D {
            problem: ThreeDProblem {
                bins: vec![Bin3D {
                    name: "loading bay".into(),
                    width: 5,
                    height: 10,
                    depth: 5,
                    cost: 1.0,
                    quantity: Some(1),
                }],
                demands: vec![BoxDemand3D {
                    name: "nested crate".into(),
                    width: 5,
                    height: 6,
                    depth: 5,
                    quantity: 2,
                    allowed_rotations: RotationMask3D::XYZ,
                }],
            },
            item_weights: vec![3],
            bin_max_weights: vec![Some(6)],
        },
        item_rules: vec![StackItemRules3D {
            nesting_height: 2,
            maximum_stackability: Some(2),
            maximum_weight_above: Some(3),
            ..StackItemRules3D::default()
        }],
        bin_rules: vec![LoadingBinRules3D {
            maximum_stack_density: Some(WeightDensity3D { numerator: 6, denominator: 25 }),
            axle_limits: Some(AxleLimits3D {
                axis: FloorAxis3D::Z,
                front_position: 0,
                rear_position: 4,
                front_maximum: 5,
                rear_maximum: 5,
                front_tare: 0,
                rear_tare: 0,
            }),
            defects: Vec::new(),
        }],
        unloading: UnloadingConstraint3D::None,
    };
    let solution = solve_loading_3d(problem.clone(), LoadingOptions3D::default())
        .expect("nested cargo with fractional reactions should solve");
    assert!(solution.unplaced.is_empty());
    assert_eq!(solution.layouts[0].stacks[0].items[1].y, 4);
    assert_eq!(solution.layouts[0].axle_loads, Some(AxleLoads3D { front: 3, rear: 4 }));
    let valid = certificate(
        "loading_3d",
        "loading nested cargo, exact density and axle reactions",
        &problem,
        &solution,
    );
    reject(cases, &valid, "loading forged nesting height", |case| {
        case["solution"]["layouts"][0]["stacks"][0]["items"][1]["y"] = json!(3);
    });
    reject(cases, &valid, "loading front reaction rounded down", |case| {
        case["solution"]["layouts"][0]["axle_loads"]["front"] = json!(2);
    });
    reject(cases, &valid, "loading maximum footprint density exceeded", |case| {
        case["problem"]["bin_rules"][0]["maximum_stack_density"]["numerator"] = json!(5);
    });
    reject(cases, &valid, "loading maximum weight above exceeded", |case| {
        case["problem"]["item_rules"][0]["maximum_weight_above"] = json!(2);
    });
    reject(cases, &valid, "loading column crosses a floor defect", |case| {
        case["problem"]["bin_rules"][0]["defects"] =
            json!([{ "x": 2, "z": 2, "width": 1, "depth": 1 }]);
    });
    cases.push(valid);

    let stock = &mut problem.packing.problem.bins[0];
    stock.width = 2;
    stock.height = 1;
    stock.depth = 1;
    problem.packing.problem.demands = vec![
        BoxDemand3D {
            name: "delivery".into(),
            width: 1,
            height: 1,
            depth: 1,
            quantity: 1,
            allowed_rotations: RotationMask3D::XYZ,
        };
        2
    ];
    problem.packing.item_weights.clear();
    problem.packing.bin_max_weights.clear();
    problem.item_rules = vec![
        StackItemRules3D::default(),
        StackItemRules3D { group_id: 1, ..StackItemRules3D::default() },
    ];
    problem.bin_rules.clear();
    problem.unloading = UnloadingConstraint3D::OnlyXMovements;
    let solution = solve_loading_3d(problem.clone(), LoadingOptions3D::default())
        .expect("delivery lanes should solve");
    assert!(solution.unplaced.is_empty());
    let valid =
        certificate("loading_3d", "loading two delivery groups in one lane", &problem, &solution);
    reject(cases, &valid, "loading later delivery group blocks the lane", |case| {
        let stacks = case["solution"]["layouts"][0]["stacks"].as_array_mut().expect("two stacks");
        let x = stacks[0]["x"].clone();
        stacks[0]["x"] = stacks[1]["x"].clone();
        stacks[1]["x"] = x;
    });
    cases.push(valid);
}

fn irregular_cases(cases: &mut Vec<Value>) {
    let circle = |x, y, radius| Shape2D {
        components: vec![Polygon2D {
            exterior: Contour2D::Circle { center: Point2D { x, y }, radius },
            holes: Vec::new(),
        }],
    };
    let mut problem = IrregularProblem {
        bins: vec![IrregularBin {
            name: "round stock".into(),
            shape: circle(5.0, 5.0, 5.0),
            quantity: Some(1),
            cost: 1.0,
            spacing: 0.0,
            defects: Vec::new(),
        }],
        demands: vec![IrregularDemand {
            name: "round detail".into(),
            shape: circle(0.0, 0.0, 5.0),
            quantity: 1,
            allowed_rotations: vec![RotationRange2D { start: 0.0, end: 0.0 }],
            can_mirror: false,
            profit: 1.0,
        }],
    };
    let options = IrregularOptions::default();
    let solution = solve_irregular(problem.clone(), options.clone()).expect("exact circle fits");
    assert!(solution.feasible);
    let input = json!({ "source": problem, "options": options });
    let valid =
        certificate("irregular_circles", "irregular equal circular boundaries", &input, &solution);
    reject(cases, &valid, "irregular circle shifted outside circular stock", |case| {
        case["solution"]["layouts"][0]["placements"][0]["x"] = json!(5.125);
    });
    cases.push(valid);

    problem.bins[0].shape = Shape2D {
        components: vec![Polygon2D {
            exterior: Contour2D::Polygon {
                vertices: vec![
                    Point2D { x: 0.0, y: 0.0 },
                    Point2D { x: 20.0, y: 0.0 },
                    Point2D { x: 20.0, y: 10.0 },
                    Point2D { x: 0.0, y: 10.0 },
                ],
            },
            holes: Vec::new(),
        }],
    };
    problem.bins[0].defects.push(circle(16.0, 6.0, 0.75));
    problem.demands[0].shape = circle(0.25, -0.125, 1.0);
    problem.demands[0].quantity = 2;
    let options = IrregularOptions {
        item_spacing: 0.5,
        defect_spacing: 0.25,
        bin_spacing: 0.125,
        ..IrregularOptions::default()
    };
    let solution = solve_irregular(problem.clone(), options.clone())
        .expect("off-origin circles and defect should solve");
    assert!(solution.feasible);
    let input = json!({ "source": problem, "options": options });
    let valid = certificate(
        "irregular_circles",
        "irregular signed centers, defect and spacing",
        &input,
        &solution,
    );
    reject(cases, &valid, "irregular overlapping discs", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[1] = placements[0].clone();
    });
    reject(cases, &valid, "irregular output weakens source spacing", |case| {
        case["solution"]["options"]["item_spacing"] = json!(0.0);
    });
    reject(cases, &valid, "irregular circle intersects protected defect", |case| {
        let x = solution.layouts[0].placements[0].x + 0.25;
        let y = solution.layouts[0].placements[0].y - 0.125;
        case["problem"]["source"]["bins"][0]["defects"][0]["components"][0]["exterior"]["center"] =
            json!({ "x": x, "y": y });
    });
    cases.push(valid);

    problem.bins[0].defects.clear();
    problem.demands[0].shape = Shape2D {
        components: vec![Polygon2D {
            exterior: Contour2D::Polygon {
                vertices: vec![
                    Point2D { x: 0.0, y: 0.0 },
                    Point2D { x: 2.0, y: 0.0 },
                    Point2D { x: 0.0, y: 1.0 },
                ],
            },
            holes: Vec::new(),
        }],
    };
    let solution =
        solve_irregular(problem.clone(), options.clone()).expect("polygonal nesting should solve");
    assert!(solution.feasible);
    let input = json!({ "source": problem, "options": options });
    let valid = certificate(
        "irregular_polygons",
        "irregular triangle hulls have a separating projection",
        &input,
        &solution,
    );
    reject(cases, &valid, "irregular transformed polygons have no separating axis", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[1] = placements[0].clone();
    });
    cases.push(valid);

    let point = |x, y| Point2D { x, y };
    let start = point(-1.5, -1.0);
    problem.demands[0].quantity = 1;
    problem.demands[0].shape.components[0].exterior = Contour2D::Curve {
        start,
        segments: vec![
            CurveSegment2D::Line { end: point(1.5, -1.0) },
            CurveSegment2D::Arc { end: point(1.5, 1.0), center: point(1.5, 0.0), clockwise: false },
            CurveSegment2D::Line { end: point(-1.5, 1.0) },
            CurveSegment2D::Arc { end: start, center: point(-1.5, 0.0), clockwise: false },
        ],
    };
    let solution = solve_irregular(problem.clone(), options.clone()).expect("curved capsule");
    assert!(solution.feasible);
    let input = json!({ "source": problem, "options": options });
    let valid = certificate("irregular_envelopes", "curved capsule envelope", &input, &solution);
    reject(cases, &valid, "curved capsule shifted through stock boundary", |case| {
        case["solution"]["layouts"][0]["placements"][0]["y"] = json!(0.5);
    });
    reject(cases, &valid, "curved contour endpoints disagree about radius", |case| {
        case["problem"]["source"]["demands"][0]["shape"]["components"][0]["exterior"]["segments"]
            [1]["end"]["y"] = json!(2.0);
        case["rejection"] = json!("arc endpoints need the same exact positive radius");
    });
    cases.push(valid);
}

fn polygon_material_cases(cases: &mut Vec<Value>) {
    let outline = |points: &[(f64, f64)]| Contour2D::Polygon {
        vertices: points.iter().map(|&(x, y)| Point2D { x, y }).collect(),
    };
    let shape = |points: &[(f64, f64)]| Shape2D {
        components: vec![Polygon2D { exterior: outline(points), holes: Vec::new() }],
    };
    let rectangle = |w, h| shape(&[(0.0, 0.0), (w, 0.0), (w, h), (0.0, h)]);
    let demand = |name: &str, shape| IrregularDemand {
        name: name.into(),
        shape,
        quantity: 1,
        allowed_rotations: vec![RotationRange2D { start: 0.0, end: 0.0 }],
        can_mirror: false,
        profit: 1.0,
    };
    let mut frame = rectangle(4.0, 4.0);
    frame.components[0].holes.push(outline(&[(1.0, 1.0), (1.0, 3.0), (3.0, 3.0), (3.0, 1.0)]));
    let mut problem = IrregularProblem {
        bins: vec![IrregularBin {
            name: "stock".into(),
            shape: rectangle(4.0, 4.0),
            cost: 1.0,
            quantity: Some(1),
            defects: Vec::new(),
            spacing: 0.0,
        }],
        demands: vec![demand("frame", frame), demand("insert", rectangle(2.0, 2.0))],
    };
    let options = IrregularOptions::default();
    let solution = solve_irregular(problem.clone(), options.clone()).expect("part fits in hole");
    assert!(solution.feasible);
    let insert = solution.layouts[0]
        .placements
        .iter()
        .position(|p| p.demand_index == 1)
        .expect("insert is placed");
    let input = json!({ "source": problem, "options": options });
    let valid = certificate(
        "irregular_orthogonal",
        "orthogonal insert occupies a material hole",
        &input,
        &solution,
    );
    reject(cases, &valid, "orthogonal insert overlaps the frame", |case| {
        case["solution"]["layouts"][0]["placements"][insert]["x"] = json!(0.75);
    });
    cases.push(valid);

    problem.bins[0].shape = rectangle(2.0, 3.0);
    problem.demands = vec![
        demand(
            "lower L",
            shape(&[(0.0, 0.0), (2.0, 0.0), (2.0, 1.0), (1.0, 1.0), (1.0, 2.0), (0.0, 2.0)]),
        ),
        demand(
            "upper L",
            shape(&[(1.0, 0.0), (2.0, 0.0), (2.0, 2.0), (0.0, 2.0), (0.0, 1.0), (1.0, 1.0)]),
        ),
    ];
    let solution =
        solve_irregular(problem.clone(), options.clone()).expect("interlocking L shapes");
    assert!(solution.feasible);
    assert_eq!(solution.layouts.len(), 1);
    let input = json!({ "source": problem, "options": options });
    cases.push(certificate(
        "irregular_orthogonal",
        "concave L shapes interlock without material overlap",
        &input,
        &solution,
    ));

    problem.bins[0].shape = rectangle(4.0, 4.0);
    problem.demands = vec![
        demand(
            "left",
            shape(&[(0.0, 0.0), (2.0, 0.0), (3.0, 1.0), (1.0, 3.0), (2.0, 4.0), (0.0, 4.0)]),
        ),
        demand(
            "right",
            shape(&[(2.0, 0.0), (4.0, 0.0), (4.0, 4.0), (2.0, 4.0), (1.0, 3.0), (3.0, 1.0)]),
        ),
    ];
    let solution =
        solve_irregular(problem.clone(), options.clone()).expect("complementary sloped outlines");
    assert!(solution.feasible);
    let right = solution.layouts[0]
        .placements
        .iter()
        .position(|p| p.demand_index == 1)
        .expect("right part");
    let input = json!({ "source": problem, "options": options });
    let valid = certificate(
        "irregular_sloped",
        "concave polygons share sloped boundaries",
        &input,
        &solution,
    );
    reject(cases, &valid, "sloped polygons have positive material overlap", |case| {
        case["solution"]["layouts"][0]["placements"][right]["x"] = json!(-0.25);
    });
    cases.push(valid);
}

fn saw_schedule_cases(cases: &mut Vec<Value>) {
    let mut job = SawJob2D {
        problem: TwoDProblem {
            sheets: vec![Sheet2D {
                name: "board".into(),
                width: 11,
                height: 4,
                cost: 1.0,
                quantity: Some(1),
                kerf: 1,
                edge_kerf_relief: false,
            }],
            demands: vec![RectDemand2D {
                name: "panel".into(),
                width: 5,
                height: 4,
                quantity: 2,
                can_rotate: false,
            }],
        },
        layouts: vec![SawLayout2D {
            width: 11,
            height: 4,
            placements: [0, 6]
                .into_iter()
                .map(|x| Placement2D {
                    name: "panel".into(),
                    x,
                    y: 0,
                    width: 5,
                    height: 4,
                    rotated: false,
                })
                .collect(),
        }],
        stock_indices: vec![0],
        demand_indices: vec![vec![0, 0]],
    };
    let options = SawPlanOptions2D::default();
    let solution = plan_saw_cuts(&job, &options).expect("table saw fixture should plan");
    assert_eq!(solution.counts.cuts, 1);
    let cut = solution
        .operations
        .iter()
        .position(|operation| matches!(operation.action, SawAction2D::Cut { .. }))
        .expect("cut operation");
    let input = json!({ "job": job, "options": options });
    let valid = certificate(
        "saw_plan",
        "saw table schedule with exact child workpieces",
        &input,
        &solution,
    );
    reject(cases, &valid, "saw cut setting differs from stop and blade offset", |case| {
        case["solution"]["operations"][cut]["action"]["setting"] = json!(4);
    });
    reject(cases, &valid, "saw operation refers to a different creating cut", |case| {
        case["solution"]["operations"][cut]["depends_on"] = json!(1);
    });
    reject(cases, &valid, "saw operation consumed workpiece without handling", |case| {
        case["solution"]["operations"].as_array_mut().expect("saw operations").remove(0);
    });
    reject(cases, &valid, "saw emitted wrong child geometry", |case| {
        case["solution"]["operations"][cut]["action"]["children"][0]["bounds"]["width"] = json!(4);
    });
    cases.push(valid);

    job.problem.sheets[0].width = 6;
    job.problem.sheets[0].height = 6;
    job.problem.sheets[0].kerf = 2;
    job.problem.sheets[0].edge_kerf_relief = true;
    job.problem.demands[0].height = 6;
    job.layouts[0].width = 6;
    job.layouts[0].height = 6;
    job.layouts[0].placements[0].height = 6;
    job.layouts[0].placements.truncate(1);
    job.demand_indices[0].truncate(1);
    let options =
        SawPlanOptions2D { machine: SawMachine2D::PanelSaw, ..SawPlanOptions2D::default() };
    let solution = plan_saw_cuts(&job, &options).expect("panel saw with clipped edge relief");
    assert_eq!(solution.counts.cuts, 1);
    let input = json!({ "job": job, "options": options });
    let valid =
        certificate("saw_plan", "saw panel schedule clips the blade at an edge", &input, &solution);
    reject(cases, &valid, "saw panel schedule clips blade on stock that forbids relief", |case| {
        case["problem"]["job"]["problem"]["sheets"][0]["edge_kerf_relief"] = json!(false);
    });
    cases.push(valid);
}

fn bar_problem(length: u32, piece: u32, quantity: usize) -> OneDProblem {
    OneDProblem {
        stock: vec![Stock1D {
            name: "bar".into(),
            length,
            kerf: 0,
            trim: 0,
            cost: 2.0,
            available: Some(1),
        }],
        demands: vec![CutDemand1D { name: "rail".into(), length: piece, quantity }],
    }
}

fn sheet_problem(stock: (u32, u32), piece: (u32, u32), quantity: usize) -> TwoDProblem {
    TwoDProblem {
        sheets: vec![Sheet2D {
            name: "sheet".into(),
            width: stock.0,
            height: stock.1,
            cost: 2.0,
            quantity: Some(1),
            kerf: 0,
            edge_kerf_relief: false,
        }],
        demands: vec![RectDemand2D {
            name: "panel".into(),
            width: piece.0,
            height: piece.1,
            quantity,
            can_rotate: false,
        }],
    }
}

fn box_problem(stock: (u32, u32, u32), piece: (u32, u32, u32), quantity: usize) -> ThreeDProblem {
    ThreeDProblem {
        bins: vec![Bin3D {
            name: "bin".into(),
            width: stock.0,
            height: stock.1,
            depth: stock.2,
            cost: 2.0,
            quantity: Some(1),
        }],
        demands: vec![BoxDemand3D {
            name: "crate".into(),
            width: piece.0,
            height: piece.1,
            depth: piece.2,
            quantity,
            allowed_rotations: RotationMask3D::XYZ,
        }],
    }
}

fn accounting_and_specialized_cases(cases: &mut Vec<Value>) {
    let mut bars = bar_problem(12, 4, 2);
    bars.stock[0].kerf = 1;
    bars.stock[0].trim = 2;
    let result = solve_1d(bars.clone(), OneDOptions::default()).expect("trimmed rail packing");
    assert!(result.unplaced.is_empty());
    let valid = certificate("accounting_1d", "1D trimmed bar with kerf", &bars, &result);
    reject(cases, &valid, "1D accounting understates total waste", |case| {
        case["solution"]["total_waste"] = json!(0);
    });
    reject(cases, &valid, "1D accounting understates total cost", |case| {
        case["solution"]["total_cost"] = json!(1);
    });
    cases.push(valid);

    let mut sheets = sheet_problem((48, 10), (24, 10), 2);
    sheets.sheets[0].kerf = 1;
    sheets.sheets[0].edge_kerf_relief = true;
    let options = TwoDOptions { seed: Some(0), ..TwoDOptions::default() };
    let ordinary = solve_2d(sheets.clone(), options.clone()).expect("stock with edge relief");
    assert_eq!(ordinary.layouts[0].placements.len(), 2);
    let valid = certificate("accounting_2d", "2D edge relief accounting", &sheets, &ordinary);
    reject(cases, &valid, "2D accounting forges used area", |case| {
        case["solution"]["layouts"][0]["used_area"] = json!(0);
    });
    cases.push(valid);

    sheets = sheet_problem((6, 6), (4, 2), 3);
    sheets.demands[0].can_rotate = true;
    let adaptive =
        solve_2d_adaptive(sheets.clone(), AdaptiveOptions2D::default()).expect("adaptive packing");
    assert_eq!(adaptive.lower_bound, lower_bound_2d(&sheets).expect("adaptive source bound"));
    for (label, result) in [
        ("demand aware", solve_2d_demand_aware(sheets.clone(), options.clone())),
        ("mixed rotations", solve_2d_mixed_rotations(sheets.clone(), options.clone())),
        ("recombined", solve_2d_recombined(sheets.clone(), options)),
        ("adaptive", Ok(adaptive.solution)),
    ] {
        let result = result.expect(label);
        assert!(result.unplaced.is_empty(), "{label}");
        let valid = certificate("2d", format!("2D {label} packing"), &sheets, &result);
        reject(cases, &valid, &format!("2D {label} part outside stock"), |case| {
            case["solution"]["layouts"][0]["placements"][0]["x"] = json!(6);
        });
        cases.push(valid);
        cases.push(certificate(
            "accounting_2d",
            format!("2D {label} accounting"),
            &sheets,
            &result,
        ));
    }

    let boxes = box_problem((6, 4, 4), (3, 4, 3), 2);
    let options = ThreeDOptions { seed: Some(0), ..ThreeDOptions::default() };
    let ordinary = solve_3d(boxes.clone(), options.clone()).expect("ordinary box packing");
    assert!(ordinary.unplaced.is_empty());
    cases.push(certificate("accounting_3d", "3D ordinary accounting", &boxes, &ordinary));
    let repaired = solve_3d_repaired(boxes.clone(), options).expect("repaired box packing");
    assert!(repaired.unplaced.is_empty());
    let valid = certificate("3d", "3D repaired packing", &boxes, &repaired);
    reject(cases, &valid, "3D repaired packing with obstructed coordinates", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[1] = placements[0].clone();
    });
    cases.push(valid);
    let valid = certificate("accounting_3d", "3D repaired accounting", &boxes, &repaired);
    reject(cases, &valid, "3D accounting forges layout waste volume", |case| {
        case["solution"]["layouts"][0]["waste_volume"] = json!(0);
    });
    cases.push(valid);
}

fn bound_cases(cases: &mut Vec<Value>) {
    let mut sheets = sheet_problem((10, 6), (6, 4), 2);
    for (name, width, height) in [("upright", 4, 6), ("short", 4, 3)] {
        sheets.demands.push(RectDemand2D {
            name: name.into(),
            width,
            height,
            ..sheets.demands[0].clone()
        });
    }
    let load = sheets
        .demands
        .iter()
        .map(|d| u64::from(d.width) * u64::from(d.height) * d.quantity as u64)
        .sum::<u64>();
    let area_bound = load.div_ceil(60);
    let geometric = lower_bound_2d(&sheets).expect("single-stock geometric bound");
    assert_eq!(area_bound, 2);
    assert_eq!(geometric, 3);
    let valid = certificate("lower_bound_2d", "2D geometric bound beats area", &sheets, &geometric);
    reject(cases, &valid, "2D inflated geometric bound", |case| {
        case["solution"] = json!(geometric + 1);
    });
    cases.push(valid);

    sheets.sheets.push(Sheet2D {
        name: "smaller stock".into(),
        width: 6,
        ..sheets.sheets[0].clone()
    });
    let area = lower_bound_2d(&sheets).expect("multi-stock area bound");
    assert_eq!(area as u64, area_bound);
    let valid = certificate("lower_bound_2d", "2D multi-stock area bound", &sheets, &area);
    reject(cases, &valid, "2D inflated multi-stock bound", |case| {
        case["solution"] = json!(area + 1);
    });
    cases.push(valid);

    let mut boxes = box_problem((5, 5, 5), (3, 3, 3), 2);
    boxes.bins[0].quantity = None;
    let options =
        ThreeDOptions { algorithm: ThreeDAlgorithm::BranchAndBound, ..ThreeDOptions::default() };
    let result = solve_3d(boxes.clone(), options).expect("exact 3D bound fixture");
    assert!(result.exact && result.unplaced.is_empty());
    let bound = result.lower_bound.expect("branch-and-bound lower bound");
    let valid = certificate("lower_bound_3d", "3D exact solver lower bound", &boxes, &bound);
    reject(cases, &valid, "3D inflated geometric bound", |case| {
        case["solution"] = json!(bound + 1.0);
    });
    cases.push(valid);
}

fn physical_sheet(problem: TwoDProblem) -> ConstrainedProblem2D {
    ConstrainedProblem2D { problem, constraints: Vec::new() }
}

fn physical_box(problem: ThreeDProblem) -> ConstrainedProblem3D {
    ConstrainedProblem3D { problem, item_weights: Vec::new(), bin_max_weights: Vec::new() }
}

fn optimization_problem<P>(packing: P) -> OptimizationProblem<P> {
    OptimizationProblem { packing, profits: Vec::new(), minimum_quantities: Vec::new() }
}

fn optimization_case(
    tag: &str,
    label: impl Into<String>,
    problem: &impl Serialize,
    options: &OptimizationOptions,
    solution: &impl Serialize,
) -> Value {
    let input = json!({ "problem": problem, "options": options });
    certificate(tag, label, &input, solution)
}

fn exact_pair(cases: &mut Vec<Value>, good: Value, worse: Value, exact_tag: &str) {
    // Both outputs must pass report and geometry checks before Lean searches for a better plan.
    for (mut case, accepted) in [(good, true), (worse, false)] {
        cases.push(case.clone());
        case["label"] = json!(format!("{exact_tag}: {}", case["label"].as_str().expect("label")));
        case["dimension"] = json!(exact_tag);
        case["accepted"] = json!(accepted);
        cases.push(case);
    }
}

fn exact_knapsack_cases(cases: &mut Vec<Value>) {
    let mut bars = bar_problem(2, 2, 1);
    bars.demands.push(CutDemand1D { name: "valuable rail".into(), ..bars.demands[0].clone() });
    let mut sheets = sheet_problem((2, 2), (2, 2), 1);
    sheets
        .demands
        .push(RectDemand2D { name: "valuable panel".into(), ..sheets.demands[0].clone() });
    let mut boxes = box_problem((2, 2, 2), (2, 2, 2), 1);
    boxes.demands.push(BoxDemand3D { name: "valuable crate".into(), ..boxes.demands[0].clone() });

    let options = OptimizationOptions {
        objective: PackingObjective::Knapsack,
        ..OptimizationOptions::default()
    };
    for (good, mut worse, exact_tag) in [
        knapsack_pair(bars, solve_1d_optimized, &options, "optimized_1d", "exact_knapsack_1d"),
        knapsack_pair(
            physical_sheet(sheets),
            solve_2d_optimized,
            &options,
            "optimized_2d",
            "exact_knapsack_2d",
        ),
        knapsack_pair(
            physical_box(boxes),
            solve_3d_optimized,
            &options,
            "optimized_3d",
            "exact_knapsack_3d",
        ),
    ] {
        worse["problem"] = good["problem"].clone();
        worse["solution"]["report"]["total_profit"] = json!(2);
        worse["solution"]["report"]["primary_value"] = json!(2);
        reject(cases, &good, &format!("{exact_tag}: forged profit"), |case| {
            case["solution"]["report"]["total_profit"] = json!(9);
        });
        reject(cases, &good, &format!("{exact_tag}: forged quantities"), |case| {
            case["solution"]["report"]["selected_quantities"] = json!([1, 1]);
        });
        reject(cases, &good, &format!("{exact_tag}: forged optimality flag"), |case| {
            case["solution"]["report"]["primary_optimal"] = json!(true);
        });
        exact_pair(cases, good, worse, exact_tag);
    }

    // Competitor stock slot sums exceeding 2^53 scaled dyadic units (2^37 + 2^-16)
    // can round in Rust binary64 and must be rejected by exact knapsack certification.
    let boundary_bars = OneDProblem {
        stock: vec![
            Stock1D {
                name: "max_exact".into(),
                length: 5,
                kerf: 0,
                trim: 0,
                cost: (1u64 << 37) as f64,
                available: Some(1),
            },
            Stock1D {
                name: "free_wide".into(),
                length: 2,
                kerf: 0,
                trim: 0,
                cost: 0.0,
                available: Some(1),
            },
            Stock1D {
                name: "tiny_exact".into(),
                length: 1,
                kerf: 0,
                trim: 0,
                cost: 1.0 / 65_536.0,
                available: Some(1),
            },
        ],
        demands: vec![
            CutDemand1D { name: "long".into(), length: 5, quantity: 1 },
            CutDemand1D { name: "short".into(), length: 1, quantity: 1 },
        ],
    };
    let boundary_source = OptimizationProblem {
        packing: boundary_bars,
        profits: vec![1.0, 1.0],
        minimum_quantities: vec![1, 1],
    };
    let boundary_out =
        solve_1d_optimized(boundary_source.clone(), options.clone()).expect("boundary knapsack");
    let boundary_rounded = optimization_case(
        "exact_knapsack_1d",
        "1D exact knapsack rejects rounded 2^37 + 2^-16 total",
        &boundary_source,
        &options,
        &boundary_out,
    );
    reject(
        cases,
        &boundary_rounded,
        "1D exact knapsack rejects rounded 2^37 + 2^-16 total",
        |case| {
            case["rejection"] = json!(
                "exact binary64 certificate requires nonnegative dyadic amounts with denominator dividing 2^16 and totals at most 2^53 / 2^16"
            );
        },
    );

    // Also test the higher-waste exact-cost layout (max_exact + free_wide, total cost 2^37):
    // optimized_1d accepts it, while exact_knapsack_1d rejects because competing slot costs
    // sum to 2^53 + 1 dyadic units.
    let mut wide_only = boundary_source.clone();
    wide_only.packing.stock.pop();
    let wide_out = solve_1d_optimized(wide_only, options.clone()).expect("wide-only knapsack");
    let mut wide_case = optimization_case(
        "optimized_1d",
        "1D optimized accepts max_exact + free_wide within 2^53 units",
        &boundary_source,
        &options,
        &wide_out,
    );
    wide_case["solution"]["effective_problem"] = json!(boundary_source.packing);
    reject(
        cases,
        &wide_case,
        "1D exact knapsack rejects competing slot cost sum exceeding 2^53 dyadic units",
        |case| {
            case["dimension"] = json!("exact_knapsack_1d");
        },
    );
    cases.push(wide_case);
}

fn knapsack_pair<P: Clone + Serialize, S: Serialize>(
    packing: P,
    solve: impl Fn(
        OptimizationProblem<P>,
        OptimizationOptions,
    ) -> bin_packing::Result<bin_packing::optimization::OptimizedSolution<S, P>>,
    options: &OptimizationOptions,
    optimized_tag: &str,
    exact_tag: &'static str,
) -> (Value, Value, &'static str) {
    let mut source =
        OptimizationProblem { packing, profits: vec![2.0, 8.0], minimum_quantities: Vec::new() };
    let best = solve(source.clone(), options.clone()).expect("profitable packing");
    assert_eq!(best.report.selected_quantities, [0, 1]);
    let good =
        optimization_case(optimized_tag, "knapsack selects higher profit", &source, options, &best);
    source.profits.reverse();
    let other = solve(source.clone(), options.clone()).expect("alternative knapsack layout");
    assert_eq!(other.report.selected_quantities, [1, 0]);
    let worse =
        optimization_case(optimized_tag, "knapsack selects lower profit", &source, options, &other);
    (good, worse, exact_tag)
}

fn exact_cost_cases(cases: &mut Vec<Value>) {
    let options = OptimizationOptions {
        objective: PackingObjective::TotalCost,
        ..OptimizationOptions::default()
    };
    let mut sheets = sheet_problem((2, 2), (2, 2), 1);
    sheets.sheets.push(Sheet2D {
        name: "expensive sheet".into(),
        cost: 8.0,
        ..sheets.sheets[0].clone()
    });
    let mut source = optimization_problem(physical_sheet(sheets));
    let best = solve_2d_optimized(source.clone(), options.clone()).expect("cheap sheet");
    assert_eq!(best.stock_indices, [0]);
    assert!(best.report.complete);
    let good =
        optimization_case("optimized_2d", "2D cheaper complete packing", &source, &options, &best);
    source.packing.problem.sheets[0].cost = 8.0;
    source.packing.problem.sheets[1].cost = 2.0;
    let other = solve_2d_optimized(source.clone(), options.clone()).expect("alternative sheet");
    assert_eq!(other.stock_indices, [1]);
    let worse =
        optimization_case("optimized_2d", "2D costly complete packing", &source, &options, &other);
    exact_pair(cases, good.clone(), reprice_cost_case(worse, &good), "exact_cost_2d");

    let mut boxes = box_problem((2, 2, 2), (2, 2, 2), 1);
    boxes.bins.push(Bin3D { name: "expensive bin".into(), cost: 8.0, ..boxes.bins[0].clone() });
    let mut source = optimization_problem(physical_box(boxes));
    let best = solve_3d_optimized(source.clone(), options.clone()).expect("cheap bin");
    assert_eq!(best.stock_indices, [0]);
    assert!(best.report.complete);
    let good =
        optimization_case("optimized_3d", "3D cheaper complete packing", &source, &options, &best);
    source.packing.problem.bins[0].cost = 8.0;
    source.packing.problem.bins[1].cost = 2.0;
    let other = solve_3d_optimized(source.clone(), options.clone()).expect("alternative bin");
    assert_eq!(other.stock_indices, [1]);
    let worse =
        optimization_case("optimized_3d", "3D costly complete packing", &source, &options, &other);
    exact_pair(cases, good.clone(), reprice_cost_case(worse, &good), "exact_cost_3d");

    let mut sheets = sheet_problem((2, 2), (2, 2), 3);
    sheets.sheets[0].quantity = Some(3);
    sheets.sheets[0].cost = 0.125;
    let source = optimization_problem(physical_sheet(sheets));
    let output = solve_2d_optimized(source.clone(), options.clone()).expect("three priced sheets");
    assert!(output.report.complete);
    assert_eq!(output.solution.sheet_count, 3);
    assert_eq!(output.solution.total_cost, 0.375);
    let valid = optimization_case(
        "exact_cost_2d",
        "2D exact cost for three dyadically priced sheets",
        &source,
        &options,
        &output,
    );
    reject(cases, &valid, "2D exact cost rejects three 0.1 sheets and forged 0.3 total", |case| {
        case["problem"]["problem"]["packing"]["problem"]["sheets"][0]["cost"] = json!(0.1);
        let output = &mut case["solution"];
        output["effective_problem"]["problem"]["sheets"][0]["cost"] = json!(0.1);
        for layout in output["solution"]["layouts"].as_array_mut().expect("priced layouts") {
            layout["cost"] = json!(0.1);
        }
        output["solution"]["total_cost"] = json!(0.3);
        output["report"]["primary_value"] = json!(0.3);
        output["report"]["primary_bound"] = json!(0.1);
        case["rejection"] = json!(concat!(
            "exact binary64 certificate requires nonnegative dyadic amounts ",
            "with denominator dividing 2^16 and totals at most 2^53 / 2^16"
        ));
    });
    cases.push(valid);
}

fn reprice_cost_case(mut worse: Value, good: &Value) -> Value {
    worse["problem"] = good["problem"].clone();
    worse["solution"]["effective_problem"] = good["solution"]["effective_problem"].clone();
    worse["solution"]["solution"]["layouts"][0]["cost"] = json!(8);
    worse["solution"]["solution"]["total_cost"] = json!(8);
    worse["solution"]["report"]["primary_value"] = json!(8);
    worse["solution"]["report"]["primary_optimal"] = json!(false);
    worse
}

fn exact_open_cases(cases: &mut Vec<Value>) {
    let mut bars = bar_problem(8, 2, 2);
    bars.stock[0].trim = 1;
    bars.stock[0].kerf = 1;
    open_pair(
        cases,
        bars,
        solve_1d_optimized,
        PackingObjective::OpenDimensionX,
        "optimized_1d",
        "exact_open_1d",
    );
    open_pair(
        cases,
        physical_sheet(sheet_problem((3, 3), (2, 1), 1)),
        solve_2d_optimized,
        PackingObjective::OpenDimensionY,
        "optimized_2d",
        "exact_open_2d",
    );
    open_pair(
        cases,
        physical_sheet(sheet_problem((3, 3), (2, 1), 1)),
        solve_2d_optimized,
        PackingObjective::OpenDimensionXy,
        "optimized_2d",
        "exact_open_2d",
    );
    open_pair(
        cases,
        physical_box(box_problem((2, 2, 4), (2, 2, 2), 1)),
        solve_3d_optimized,
        PackingObjective::OpenDimensionZ,
        "optimized_3d",
        "exact_open_3d",
    );

    let source = optimization_problem(bar_problem(4, 1, 3));
    let options = OptimizationOptions {
        objective: PackingObjective::OpenDimensionX,
        ..OptimizationOptions::default()
    };
    let mut output =
        solve_1d_optimized(source.clone(), options.clone()).expect("minimum open bar extent");
    assert!(output.report.complete);
    assert_eq!(output.report.open_extents, [3]);
    output.solution.unplaced = output.solution.layouts.drain(..).flat_map(|row| row.cuts).collect();
    assert_eq!(output.solution.unplaced.len(), 3);
    output.solution.stock_count = 0;
    output.solution.stock_requirements.clear();
    output.solution.total_cost = 0.0;
    output.solution.total_waste = 0;
    output.solution.exact = false;
    output.solution.lower_bound = None;
    output.stock_indices.clear();
    output.demand_indices.clear();
    output.report.selected_quantities = vec![0];
    output.report.complete = false;
    output.report.total_profit = 0.0;
    output.report.primary_optimal = false;
    let partial = optimization_case(
        "optimized_1d",
        "1D open report accounts for every unplaced cut at the minimum extent",
        &source,
        &options,
        &output,
    );
    reject(
        cases,
        &partial,
        "1D exact open rejects an empty incumbent at the minimum extent",
        |case| {
            case["dimension"] = json!("exact_open_1d");
        },
    );
    cases.push(partial);
}

fn open_pair<P: Clone + Serialize, S: Serialize>(
    cases: &mut Vec<Value>,
    packing: P,
    solve: impl Fn(
        OptimizationProblem<P>,
        OptimizationOptions,
    ) -> bin_packing::Result<bin_packing::optimization::OptimizedSolution<S, P>>,
    objective: PackingObjective,
    optimized_tag: &str,
    exact_tag: &str,
) {
    let source = optimization_problem(packing);
    let options = OptimizationOptions { objective, ..OptimizationOptions::default() };
    let best = solve(source.clone(), options.clone()).expect("open dimension can shrink");
    let good =
        optimization_case(optimized_tag, format!("{objective:?} crop"), &source, &options, &best);
    let short_search = OptimizationOptions { max_evaluations: 1, ..options };
    let other = solve(source.clone(), short_search.clone()).expect("uncropped layout fits");
    assert!(best.report.complete && other.report.complete);
    assert!(best.report.primary_value < other.report.primary_value);
    let worse = optimization_case(
        optimized_tag,
        format!("{objective:?} nonminimal extent"),
        &source,
        &short_search,
        &other,
    );
    exact_pair(cases, good, worse, exact_tag);
}

fn other_optimization_cases(cases: &mut Vec<Value>) {
    let problem = optimization_problem(bar_problem(3, 2, 2));
    let options = OptimizationOptions {
        objective: PackingObjective::Feasibility,
        ..OptimizationOptions::default()
    };
    let output = solve_1d_optimized(problem.clone(), options.clone()).expect("partial capped bar");
    assert!(!output.report.complete);
    cases.push(optimization_case(
        "optimized_1d",
        "1D feasibility with shortage",
        &problem,
        &options,
        &output,
    ));

    let problem = optimization_problem(StagedProblem2D {
        packing: physical_sheet(sheet_problem((4, 2), (2, 2), 2)),
        rules: StagedRules2D {
            max_stages: Some(1),
            cut_type: StagedCutType2D::Exact,
            ..StagedRules2D::default()
        },
        groups: vec![Some(1)],
    });
    let options = OptimizationOptions::default();
    let output =
        solve_2d_staged_optimized(problem.clone(), options.clone()).expect("staged bin count");
    assert!(output.report.complete);
    let valid = optimization_case(
        "optimized_staged_2d",
        "2D staged bin count",
        &problem,
        &options,
        &output,
    );
    reject(cases, &valid, "2D staged optimization forges quantities", |case| {
        case["solution"]["report"]["selected_quantities"] = json!([1]);
    });
    cases.push(valid);

    let mut packing = physical_sheet(sheet_problem((4, 4), (2, 2), 1));
    packing.constraints.push(SheetConstraints2D {
        defects: vec![Defect2D { x: 1, y: 3, width: 3, height: 1 }],
        ..SheetConstraints2D::default()
    });
    let problem = optimization_problem(packing);
    let options = OptimizationOptions {
        objective: PackingObjective::OpenDimensionX,
        ..OptimizationOptions::default()
    };
    let output =
        solve_2d_optimized(problem.clone(), options.clone()).expect("sheet crop clips a defect");
    assert!(output.report.complete);
    assert_eq!(output.report.open_extents, [2, 4]);
    assert_eq!(output.effective_problem.constraints[0].defects[0].width, 1);
    let valid = optimization_case(
        "optimized_2d",
        "2D open crop clips a defect",
        &problem,
        &options,
        &output,
    );
    reject(cases, &valid, "2D open crop drops its surviving defect", |case| {
        case["solution"]["effective_problem"]["constraints"][0]["defects"] = json!([]);
    });
    cases.push(valid);

    let mut packing = physical_box(box_problem((2, 2, 4), (2, 2, 2), 1));
    packing.item_weights = vec![2];
    let problem = optimization_problem(LoadingProblem3D {
        packing,
        item_rules: Vec::new(),
        bin_rules: vec![LoadingBinRules3D {
            axle_limits: Some(AxleLimits3D {
                axis: FloorAxis3D::Z,
                front_position: 0,
                rear_position: 2,
                front_maximum: 4,
                rear_maximum: 4,
                front_tare: 0,
                rear_tare: 0,
            }),
            ..LoadingBinRules3D::default()
        }],
        unloading: UnloadingConstraint3D::None,
    });
    let options = OptimizationOptions {
        objective: PackingObjective::OpenDimensionZ,
        ..OptimizationOptions::default()
    };
    let output = solve_loading_3d_optimized(problem.clone(), options.clone())
        .expect("loading crop retains axle");
    assert!(output.report.complete);
    assert_eq!(output.report.open_extents, [2, 2, 2]);
    let valid = optimization_case(
        "optimized_loading_3d",
        "3D open loading preserves axle",
        &problem,
        &options,
        &output,
    );
    reject(cases, &valid, "3D open loading changes the fixed rear axle", |case| {
        case["solution"]["effective_problem"]["bin_rules"][0]["axle_limits"]["rear_position"] =
            json!(1);
    });
    cases.push(valid);
}

fn infeasible_cases(cases: &mut Vec<Value>) {
    let bars = bar_problem(3, 2, 1);
    let sheets = sheet_problem((3, 2), (2, 2), 1);
    let boxes = box_problem((3, 2, 2), (2, 2, 2), 1);
    let linear = |p| solve_1d(p, OneDOptions::default());
    let planar = |p| solve_2d(p, TwoDOptions::default());
    let spatial = |p| solve_3d(p, ThreeDOptions::default());
    assert!(linear(bars.clone()).expect("feasible bar").unplaced.is_empty());
    assert!(planar(sheets.clone()).expect("feasible sheet").unplaced.is_empty());
    assert!(spatial(boxes.clone()).expect("feasible bin").unplaced.is_empty());
    let feasible =
        [json!(bars), json!(physical_sheet(sheets.clone())), json!(physical_box(boxes.clone()))];

    for witness in ["oversize", "inventory", "exhaustive"] {
        let (mut bars, mut sheets, mut boxes) = (bars.clone(), sheets.clone(), boxes.clone());
        if witness == "oversize" {
            bars.demands[0].length = 4;
            sheets.demands[0].width = 4;
            boxes.demands[0].width = 4;
            assert!(matches!(
                linear(bars.clone()),
                Err(BinPackingError::Infeasible1D { length: 4, .. })
            ));
            assert!(matches!(
                planar(sheets.clone()),
                Err(BinPackingError::Infeasible2D { width: 4, .. })
            ));
            assert!(matches!(
                spatial(boxes.clone()),
                Err(BinPackingError::Infeasible3D { width: 4, .. })
            ));
        } else {
            bars.demands[0].quantity = 3;
            sheets.demands[0].quantity = 3;
            boxes.demands[0].quantity = 3;
            if witness == "exhaustive" {
                // Two slots have sufficient total material, but each holds only one part.
                bars.stock[0].available = Some(2);
                sheets.sheets[0].quantity = Some(2);
                boxes.bins[0].quantity = Some(2);
            }
            assert!(!linear(bars.clone()).expect("partial bar packing").unplaced.is_empty());
            assert!(!planar(sheets.clone()).expect("partial sheet packing").unplaced.is_empty());
            assert!(!spatial(boxes.clone()).expect("partial bin packing").unplaced.is_empty());
        }
        let problems = [json!(bars), json!(physical_sheet(sheets)), json!(physical_box(boxes))];
        for ((tag, problem), feasible) in ["infeasible_1d", "infeasible_2d", "infeasible_3d"]
            .into_iter()
            .zip(problems)
            .zip(&feasible)
        {
            let valid = certificate(tag, format!("{tag}: {witness} witness"), &problem, &witness);
            reject(cases, &valid, &format!("{tag}: false {witness} witness"), |case| {
                case["problem"] = feasible.clone();
            });
            cases.push(valid);
        }
    }

    // Keep the input compact and let Lean check the witness directly from the rows.
    let quantity = 1_000_000;
    let mut bars = bar_problem(3, 4, quantity);
    let mut sheets = sheet_problem((3, 2), (4, 2), quantity);
    bars.stock[0].available = None;
    sheets.sheets[0].quantity = None;
    cases.push(certificate("infeasible_1d", "1D oversize with a million cuts", &bars, &"oversize"));
    cases.push(certificate(
        "infeasible_2d",
        "2D oversize with a million parts",
        &physical_sheet(sheets.clone()),
        &"oversize",
    ));
    bars.demands[0].length = 2;
    sheets.demands[0].width = 2;
    bars.stock[0].available = Some(quantity / 2);
    sheets.sheets[0].quantity = Some(quantity / 2);
    cases.push(certificate(
        "infeasible_1d",
        "1D inventory with a million cuts",
        &bars,
        &"inventory",
    ));
    cases.push(certificate(
        "infeasible_2d",
        "2D inventory with a million parts",
        &physical_sheet(sheets),
        &"inventory",
    ));
}

fn reuse_cases(cases: &mut Vec<Value>) {
    let mut problem = sheet_problem((8, 4), (2, 4), 1);
    problem.sheets[0].kerf = 1;
    let forecast = ReuseForecast2D {
        demands: vec![ForecastPart2D {
            width: 2,
            height: 4,
            quantity: 2,
            can_rotate: false,
            weight: 3.0,
        }],
    };
    // One candidate makes the returned selected job the baseline witness too.
    let options = ReuseOptions2D { max_candidate_solves: 1, ..ReuseOptions2D::default() };
    let solver = TwoDOptions { algorithm: TwoDAlgorithm::Guillotine, ..TwoDOptions::default() };
    let output = solve_2d_with_reuse(problem.clone(), solver, &forecast, &options)
        .expect("reuse solver leaves an offcut");
    assert!(output.solution.unplaced.is_empty());
    let evaluation = evaluate_reuse(&output.job, &forecast, &options).expect("offcut evaluation");
    assert_eq!(evaluation, output.evaluation);
    assert_eq!(evaluation.fulfilled_counts, [2]);
    assert_eq!(evaluation.placements.len(), 2);
    let saw_options = SawPlanOptions2D {
        search: SawSearchLimits2D {
            max_states: 0,
            baseline_max_states: 10_000,
            ..SawSearchLimits2D::default()
        },
        ..SawPlanOptions2D::default()
    };
    let saw_plan = plan_saw_cuts(&output.job, &saw_options).expect("saw witness for reuse");
    let blade_strip = SawRect2D { x: 2, y: 0, width: 1, height: 4 };
    assert!(saw_plan.operations.iter().any(|operation| {
        matches!(operation.action, SawAction2D::Cut { kerf_region, .. } if kerf_region == blade_strip)
    }));
    let input = json!({
        "job": output.job, "forecast": forecast, "options": options, "saw_plan": saw_plan,
    });
    let valid =
        certificate("reuse_eval_2d", "reuse evaluates two future parts", &input, &evaluation);
    reject(cases, &valid, "reuse future placements overlap", |case| {
        let placements = &mut case["solution"]["placements"];
        placements[1] = placements[0].clone();
    });
    reject(cases, &valid, "reuse weighted fulfillment is wrong", |case| {
        case["solution"]["weighted_fulfillment"] = json!(3);
    });
    reject(cases, &valid, "reuse claims blade-removed kerf as a forecast offcut", |case| {
        case["problem"]["forecast"]["demands"][0]["width"] = json!(1);
        let output = &mut case["solution"];
        output["offcuts"][0]["workpiece"]["bounds"] = json!(blade_strip);
        let placements = output["placements"].as_array_mut().expect("future placements");
        placements.truncate(1);
        placements[0]["bounds"] = json!(blade_strip);
        output["fulfilled_counts"] = json!([1]);
        output["weighted_fulfillment"] = json!(3);
    });
    cases.push(valid);

    let input = json!({
        "problem": problem, "forecast": forecast, "options": options, "saw_plan": saw_plan,
    });
    let valid = certificate(
        "reuse_solve_2d",
        "reuse certifies selected and baseline layouts",
        &input,
        &output,
    );
    reject(cases, &valid, "reuse selected stock exceeds material ceiling", |case| {
        case["problem"]["options"]["max_material_cost"] = json!(1);
    });
    cases.push(valid);

    let budget = ReuseOptions2D { max_material_cost: Some(1.0), ..options.clone() };
    assert!(matches!(
        evaluate_reuse(&output.job, &forecast, &budget),
        Err(ReuseError2D::MaterialBudget { sheet_count: 1, cost }) if cost == 2.0
    ));
    let mut invalid = forecast.clone();
    invalid.demands[0].width = 0;
    assert!(matches!(
        evaluate_reuse(&output.job, &invalid, &options),
        Err(ReuseError2D::InvalidForecast { index: 0, .. })
    ));
    let options = ReuseOptions2D { max_future_parts: 0, ..options };
    assert!(matches!(
        solve_2d_with_reuse(problem, TwoDOptions::default(), &forecast, &options),
        Err(ReuseError2D::InvalidOption { field: "search limits" })
    ));
}

fn legacy_cut_plan_cases(cases: &mut Vec<Value>) {
    let mut bars = bar_problem(11, 4, 2);
    bars.stock[0].kerf = 1;
    bars.stock[0].trim = 1;
    let result = solve_1d(bars.clone(), OneDOptions::default()).expect("cut-plan bar packing");
    let options = CutPlanOptions1D {
        cut_cost: Some(1.25),
        fence_reset_cost: Some(0.5),
        ..CutPlanOptions1D::default()
    };
    let plan = bar_plan::plan_cuts(&bars, &result, &options).expect("bar cut plan");
    let cut = plan.bar_plans[0]
        .steps
        .iter()
        .position(|step| matches!(step, CutStep1D::Cut { .. }))
        .expect("bar separating cut");
    let input = json!({ "problem": bars, "solution": result, "options": options });
    let valid = certificate("cut_plan_1d", "legacy chop saw replays kerf with trim", &input, &plan);
    reject(cases, &valid, "legacy chop saw forges cut position", |case| {
        case["solution"]["bar_plans"][0]["steps"][cut]["position"] = json!(0);
    });
    reject(cases, &valid, "legacy chop saw forges total cost", |case| {
        case["solution"]["total_cost"] = json!(0);
    });
    cases.push(valid);

    let defaults = CutPlanOptions1D::default();
    let default_plan =
        bar_plan::plan_cuts(&bars, &result, &defaults).expect("bar plan with default prices");
    assert_eq!(default_plan.effective_costs.fence_reset_cost, 0.3);
    let input = json!({ "problem": bars, "solution": result, "options": defaults });
    let mut non_dyadic = certificate(
        "cut_plan_1d",
        "legacy chop saw rejects default 0.3 reset cost",
        &input,
        &default_plan,
    );
    non_dyadic["accepted"] = json!(false);
    non_dyadic["rejection"] = json!(concat!(
        "options.fence_reset_cost: exact binary64 certification requires nonnegative dyadic ",
        "prices and costs (integers or multiples of 2^-k with k ≤ 16)"
    ));
    cases.push(non_dyadic);

    let options = CutPlanOptions1D { cut_cost: Some(-1.0), ..options };
    assert!(matches!(
        bar_plan::plan_cuts(&bars, &result, &options),
        Err(CutPlanError::InvalidOptions(_))
    ));

    let sheets = sheet_problem((6, 2), (2, 2), 2);
    let solver = TwoDOptions { algorithm: TwoDAlgorithm::Guillotine, ..TwoDOptions::default() };
    let result = solve_2d(sheets, solver.clone()).expect("cut-plan sheet packing");
    assert!(result.guillotine && result.unplaced.is_empty());
    let prices = CutPlanOptions2D {
        cut_cost: Some(1.0),
        fence_reset_cost: Some(0.5),
        rotate_cost: Some(2.0),
        tool_up_down_cost: Some(0.25),
        travel_cost: Some(0.125),
        ..CutPlanOptions2D::default()
    };
    for preset in [CutPlanPreset2D::TableSaw, CutPlanPreset2D::PanelSaw, CutPlanPreset2D::CncRouter]
    {
        let options = CutPlanOptions2D { preset, ..prices };
        let plan = sheet_plan::plan_cuts(&result, &options).expect("legacy sheet cut plan");
        let input = json!({ "solution": result, "options": options });
        let valid = certificate(
            "cut_plan_2d",
            format!("legacy {preset:?} produces all parts"),
            &input,
            &plan,
        );
        if preset == CutPlanPreset2D::CncRouter {
            let lift = plan.sheet_plans[0]
                .steps
                .iter()
                .rposition(|step| matches!(step, CutStep2D::ToolUp))
                .expect("router lifts tool");
            reject(cases, &valid, "legacy router tool sequence is unbalanced", |case| {
                case["solution"]["sheet_plans"][0]["steps"][lift] = json!({ "kind": "tool_down" });
            });
        } else {
            let cut = plan.sheet_plans[0]
                .steps
                .iter()
                .position(|step| matches!(step, CutStep2D::Cut { .. }))
                .expect("sheet separating cut");
            reject(cases, &valid, &format!("legacy {preset:?} moves the cut"), |case| {
                case["solution"]["sheet_plans"][0]["steps"][cut]["position"] = json!(0);
            });
        }
        reject(cases, &valid, &format!("legacy {preset:?} forges total cost"), |case| {
            case["solution"]["total_cost"] = json!(0);
        });
        cases.push(valid);
    }
    let options =
        CutPlanOptions2D { travel_cost: Some(f64::INFINITY), ..CutPlanOptions2D::default() };
    assert!(matches!(
        sheet_plan::plan_cuts(&result, &options),
        Err(CutPlanError::InvalidOptions(_))
    ));

    let mut sheets = sheet_problem((48, 10), (24, 10), 2);
    sheets.sheets[0].kerf = 1;
    sheets.sheets[0].edge_kerf_relief = true;
    let result = solve_2d(sheets, solver).expect("edge-relief guillotine packing");
    assert!(result.unplaced.is_empty());
    assert_eq!(result.sheet_count, 1);
    let width = result.layouts[0].width;
    assert_eq!(width, 48);
    let options = CutPlanOptions2D { preset: CutPlanPreset2D::CncRouter, ..prices };
    let plan =
        sheet_plan::plan_cuts(&result, &options).expect("router plans the overhanging outline");
    assert!(
        plan.sheet_plans[0]
            .steps
            .iter()
            .any(|step| { matches!(step, CutStep2D::LineCut { to_x, .. } if *to_x == width + 1) })
    );
    let input = json!({ "solution": result, "options": options });
    let mut overhang = certificate(
        "cut_plan_2d",
        "legacy router cuts past the physical sheet edge",
        &input,
        &plan,
    );
    overhang["accepted"] = json!(false);
    cases.push(overhang);
}

fn irregular_exact_cases(cases: &mut Vec<Value>) {
    let point = |x, y| Point2D { x, y };
    let outline = |vertices: &[(f64, f64)]| Contour2D::Polygon {
        vertices: vertices.iter().map(|&(x, y)| point(x, y)).collect(),
    };
    let shape = |exterior, holes| Shape2D { components: vec![Polygon2D { exterior, holes }] };
    let stock = shape(outline(&[(0.0, 0.0), (40.0, 0.0), (40.0, 20.0), (0.0, 20.0)]), vec![]);
    let defect = shape(outline(&[(30.0, 8.0), (32.0, 8.0), (32.0, 10.0), (30.0, 10.0)]), vec![]);
    let sloped = shape(
        outline(&[(0.0, 0.0), (6.0, 0.0), (6.0, 4.0), (3.0, 3.0), (0.0, 4.0)]),
        vec![outline(&[(1.0, 1.0), (1.0, 2.0), (2.0, 2.0), (2.0, 1.0)])],
    );
    let mut source = IrregularProblem {
        bins: vec![IrregularBin {
            name: "stock".into(),
            shape: stock,
            cost: 2.0,
            quantity: Some(1),
            defects: vec![defect],
            spacing: 0.0,
        }],
        demands: vec![IrregularDemand {
            name: "sloped part".into(),
            shape: sloped,
            quantity: 2,
            allowed_rotations: vec![RotationRange2D { start: 0.0, end: 0.0 }],
            can_mirror: false,
            profit: 1.0,
        }],
    };
    let options = IrregularOptions {
        item_spacing: 0.5,
        bin_spacing: 0.5,
        defect_spacing: 0.5,
        ..IrregularOptions::default()
    };
    let output = solve_irregular(source.clone(), options.clone()).expect("sloped parts with holes");
    assert!(output.feasible);
    validate_irregular(&source, &output).expect("validate sloped solution");
    let input = json!({ "source": source, "options": options });
    let valid = certificate(
        "irregular_sloped_cleared",
        "sloped concave stock parts with holes and positive spacing",
        &input,
        &output,
    );
    let mut forged = output;
    forged.options.item_spacing = 40.0;
    assert!(matches!(
        validate_irregular(&source, &forged),
        Err(BinPackingError::InvalidSolution { .. })
    ));
    reject(
        cases,
        &valid,
        "sloped parts fail required clearance with transforms unchanged",
        |case| {
            case["problem"]["options"]["item_spacing"] = json!(40);
            case["solution"] = json!(forged);
        },
    );
    reject(cases, &valid, "sloped part fails positive boundary clearance", |case| {
        case["solution"]["layouts"][0]["placements"][0]["x"] = json!(0);
    });
    assert_eq!(
        valid["solution"]["layouts"][0]["placements"].as_array().expect("sloped placements").len(),
        2
    );
    reject(cases, &valid, "sloped coincident parts have holes equal to their exteriors", |case| {
        let component = &mut case["problem"]["source"]["demands"][0]["shape"]["components"][0];
        component["holes"] = json!([component["exterior"]]);
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[1] = placements[0].clone();
        case["rejection"] = json!("polygon hole must lie strictly inside its exterior");
    });
    reject(cases, &valid, "sloped ring self-crosses with nonzero signed area", |case| {
        let component = &mut case["problem"]["source"]["demands"][0]["shape"]["components"][0];
        component["exterior"] = json!({
            "kind": "polygon",
            "vertices": [
                { "x": 0.0, "y": 0.0 },
                { "x": 4.0, "y": 0.0 },
                { "x": 1.0, "y": 3.0 },
                { "x": 3.0, "y": 3.0 },
            ],
        });
        component["holes"] = json!([]);
        case["rejection"] =
            json!("polygon ring has intersecting edges or collinear consecutive edges");
    });
    reject(cases, &valid, "sloped ring has all collinear vertices", |case| {
        let component = &mut case["problem"]["source"]["demands"][0]["shape"]["components"][0];
        component["exterior"] = json!({
            "kind": "polygon",
            "vertices": [
                { "x": 0.0, "y": 0.0 },
                { "x": 2.0, "y": 2.0 },
                { "x": 4.0, "y": 4.0 },
            ],
        });
        component["holes"] = json!([]);
        case["rejection"] = json!("polygon ring has zero signed area");
    });
    cases.push(valid);

    let start = point(-1.5, -1.0);
    source.demands[0].name = "capsule".into();
    source.demands[0].shape = shape(
        Contour2D::Curve {
            start,
            segments: vec![
                CurveSegment2D::Line { end: point(1.5, -1.0) },
                CurveSegment2D::Arc {
                    end: point(1.5, 1.0),
                    center: point(1.5, 0.0),
                    clockwise: false,
                },
                CurveSegment2D::Line { end: point(-1.5, 1.0) },
                CurveSegment2D::Arc { end: start, center: point(-1.5, 0.0), clockwise: false },
            ],
        },
        vec![],
    );
    source.demands[0].allowed_rotations = vec![RotationRange2D { start: 45.0, end: 45.0 }];
    // Allow room for Lean's conservative arc and general-angle envelopes.
    let padded = IrregularOptions {
        item_spacing: 8.0,
        bin_spacing: 5.0,
        defect_spacing: 5.0,
        ..options.clone()
    };
    let mut output = solve_irregular(source.clone(), padded).expect("angled capsules");
    output.options = options.clone();
    assert!(output.feasible);
    assert_eq!(output.layouts[0].placements[0].rotation_degrees, 45.0);
    validate_irregular(&source, &output).expect("validate capsule solution and clearance");
    let input = json!({ "source": source, "options": options });
    let valid =
        certificate("irregular_curved_exact", "curved capsule arcs at 45 degrees", &input, &output);
    reject(cases, &valid, "angled capsule arcs overlap", |case| {
        let placements = &mut case["solution"]["layouts"][0]["placements"];
        placements[1] = placements[0].clone();
    });
    cases.push(valid);
}

#[test]
fn solvers_reject_invalid_boundary_inputs() {
    let invalid = bar_problem(2, 0, 1);
    assert!(matches!(
        solve_1d(invalid, OneDOptions::default()),
        Err(BinPackingError::InvalidInput(_))
    ));
    let invalid = sheet_problem((3, 3), (2, 2), 0);
    assert!(matches!(lower_bound_2d(&invalid), Err(BinPackingError::InvalidInput(_))));
    let mut invalid = box_problem((3, 3, 3), (2, 2, 2), 1);
    invalid.bins[0].cost = f64::NAN;
    assert!(matches!(
        solve_3d_repaired(invalid, ThreeDOptions::default()),
        Err(BinPackingError::InvalidInput(_))
    ));
    let options = AdaptiveOptions2D { max_candidates: 12, ..AdaptiveOptions2D::default() };
    assert!(matches!(
        solve_2d_adaptive(sheet_problem((3, 3), (2, 2), 1), options),
        Err(BinPackingError::InvalidConstraint { field, .. }) if field == "max_candidates"
    ));
    let options = OptimizationOptions { max_evaluations: 0, ..OptimizationOptions::default() };
    assert!(matches!(
        solve_1d_optimized(optimization_problem(bar_problem(3, 2, 1)), options),
        Err(BinPackingError::InvalidConstraint { field, .. }) if field == "search"
    ));
}

#[test]
#[ignore = "requires the pinned Lean toolchain; run scripts/check-proofs.sh"]
fn lean_checks_solver_certificates() {
    let mut cases = Vec::new();
    linear_cases(&mut cases);
    sheet_cases(&mut cases);
    box_cases(&mut cases);
    constrained_cases(&mut cases);
    staged_cases(&mut cases);
    loading_cases(&mut cases);
    irregular_cases(&mut cases);
    polygon_material_cases(&mut cases);
    saw_schedule_cases(&mut cases);
    accounting_and_specialized_cases(&mut cases);
    bound_cases(&mut cases);
    exact_knapsack_cases(&mut cases);
    exact_cost_cases(&mut cases);
    exact_open_cases(&mut cases);
    other_optimization_cases(&mut cases);
    infeasible_cases(&mut cases);
    reuse_cases(&mut cases);
    legacy_cut_plan_cases(&mut cases);
    irregular_exact_cases(&mut cases);

    let proofs = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs");
    let toolchain = fs::read_to_string(proofs.join("lean-toolchain")).expect("Lean toolchain pin");
    let json = serde_json::to_vec(&cases).expect("serialize Rust solver output");
    let built = Command::new("elan")
        .current_dir(&proofs)
        .args(["run", toolchain.trim(), "lake", "build", "Packing"])
        .status()
        .expect("build Lean proof modules via elan");
    assert!(built.success(), "Lean module build failed");

    let mut checker = Command::new("elan")
        .current_dir(proofs)
        .args(["run", toolchain.trim(), "lake", "env", "lean", "--run", "Check.lean"])
        .stdin(Stdio::piped())
        .spawn()
        .expect("start Lean via elan");
    let sent = checker.stdin.take().expect("Lean input pipe").write_all(&json);
    assert!(checker.wait().expect("wait for Lean").success(), "Lean certificate check failed");
    sent.expect("send Rust solver output to Lean");
}
