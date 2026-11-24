// Emit real package outputs for the Lean checker's test runner.
const assert = require('node:assert/strict');

const backends = [
  ['Node', require('../node')],
  ['WebAssembly', require('../wasm/dist/nodejs/bin_packing_wasm.cjs')],
];

const stock = {
  stock: [{ name: 'bar', length: 11, trim: 1, kerf: 2 }],
  demands: [{ name: 'rail', length: 4, quantity: 3 }],
};

const freeStock = {
  stock: [{ name: 'long', length: 12, cost: 0 }, { name: 'short', length: 6, cost: -0 }],
  demands: [{ name: 'rail', length: 6, quantity: 2 }],
};

const gridSheet = {
  sheets: [{ name: 'square', width: 5, height: 5 }],
  demands: [{ name: 'tile', width: 3, height: 3, quantity: 2, can_rotate: false }],
};

const gridBin = {
  bins: [{ name: 'cube', width: 5, height: 5, depth: 5 }],
  demands: [{
    name: 'box', width: 3, height: 3, depth: 3, quantity: 2, allowed_rotations: 1,
  }],
};

const sheet = {
  sheets: [{
    name: 'sheet', width: 48, height: 10, cost: 1, quantity: 1, kerf: 1,
    edge_kerf_relief: true,
  }],
  demands: [{ name: 'panel', width: 24, height: 10, quantity: 3, can_rotate: false }],
};

const staged = {
  packing: {
    problem: {
      sheets: [{ name: 'board', width: 11, height: 4, kerf: 1, quantity: 1 }],
      demands: [{ name: 'strip', width: 5, height: 4, quantity: 2 }],
    },
  },
  rules: { max_stages: 1, cut_type: 'exact' },
};

const loading = {
  packing: {
    problem: {
      bins: [{ name: 'bay', width: 2, height: 9, depth: 2, cost: 1, quantity: 1 }],
      demands: [{
        name: 'box', width: 2, height: 6, depth: 2, quantity: 2,
      }],
    },
    item_weights: [3],
    bin_max_weights: [6],
  },
  item_rules: [{
    stackability_id: 7,
    nesting_height: 3,
    maximum_stackability: 2,
    maximum_weight_above: 3,
  }],
  bin_rules: [{
    maximum_stack_density: { numerator: 3, denominator: 2 },
    axle_limits: {
      axis: 'z',
      front_position: 0,
      rear_position: 2,
      front_maximum: 4,
      rear_maximum: 5,
      front_tare: 1,
      rear_tare: 2,
    },
  }],
};

function checkOptimizationCases(api, check) {
  function optimize(method, dimensions, problem, objective, label) {
    const options = { objective };
    const solution = api[method](problem, options);
    check(dimensions, `${method} ${label}`, { problem, options }, solution);
    return solution;
  }

  for (const objective of ['bin_count', 'total_cost', 'feasibility']) {
    const solution = optimize('solve1dOptimized', ['optimized_1d'], { packing: stock }, objective, objective);
    assert.equal(solution.report.complete, true);
  }

  const linearOpen = { ...stock, stock: [{ ...stock.stock[0], length: 20 }] };
  const openBar = optimize('solve1dOptimized', ['optimized_1d', 'exact_open_1d'],
    { packing: linearOpen }, 'open_dimension_x', 'shrinks bar including trim and kerf');
  assert.deepEqual(openBar.report.open_extents, [17]);

  const incompleteBar = structuredClone(openBar);
  const unplaced = incompleteBar.solution.layouts.flatMap(layout => layout.cuts);
  Object.assign(incompleteBar.solution, {
    stock_count: 0, total_cost: 0, total_waste: 0, layouts: [], unplaced,
  });
  incompleteBar.stock_indices = [];
  incompleteBar.demand_indices = [];
  Object.assign(incompleteBar.report, {
    complete: false, primary_optimal: false, selected_quantities: [0], total_profit: 0,
  });
  const openBarInput = { problem: { packing: linearOpen }, options: { objective: 'open_dimension_x' } };
  check(['optimized_1d'], 'valid readback of an incomplete incumbent', openBarInput, incompleteBar);
  check(['exact_open_1d'], 'incomplete incumbent at minimum extent', openBarInput, incompleteBar, false);

  const sheetStock = gridSheet.sheets[0];
  const binStock = gridBin.bins[0];
  const profitNames = ['low profit', 'high profit'];
  const linearKnapsack = {
    stock: [{ name: 'one bar', length: 6, available: 1 }],
    demands: profitNames.map(name => ({ name, length: 6, quantity: 1 })),
  };
  const sheetKnapsack = {
    problem: {
      sheets: [{ ...sheetStock, quantity: 1 }],
      demands: profitNames.map(name => ({ ...gridSheet.demands[0], name, quantity: 1 })),
    },
  };
  const binKnapsack = {
    problem: {
      bins: [{ ...binStock, quantity: 1 }],
      demands: profitNames.map(name => ({ ...gridBin.demands[0], name, quantity: 1 })),
    },
    item_weights: [1, 2],
    bin_max_weights: [2],
  };
  for (const [dimension, method, packing] of [
    ['1d', 'solve1dOptimized', linearKnapsack],
    ['2d', 'solve2dOptimized', sheetKnapsack],
    ['3d', 'solve3dOptimized', binKnapsack],
  ]) {
    const problem = { packing, profits: [1, 4] };
    const options = { objective: 'knapsack' };
    const solution = optimize(method, [`optimized_${dimension}`, `exact_knapsack_${dimension}`],
      problem, options.objective, 'chooses higher profit under limited inventory');
    assert.deepEqual(solution.report.selected_quantities, [0, 1]);
    if (dimension === '1d') {
      const forged = structuredClone(solution);
      forged.report.total_profit += 1;
      check(['optimized_1d'], 'forged optimization profit', { problem, options }, forged, false);
    }
  }

  for (const [dimension, method, name, base] of [
    ['2d', 'solve2dOptimized', 'sheets', gridSheet],
    ['3d', 'solve3dOptimized', 'bins', gridBin],
  ]) {
    const template = base[name][0];
    const packing = { problem: {
      [name]: [
        { ...template, name: 'premium', quantity: 1, cost: 7 },
        { ...template, name: 'economy', quantity: 1, cost: 2 },
      ],
      demands: [{ ...base.demands[0], quantity: 1 }],
    } };
    const solution = optimize(method, [`optimized_${dimension}`, `exact_cost_${dimension}`],
      { packing }, 'total_cost', 'selects cheaper stock');
    assert.equal(solution.solution.total_cost, 2);
  }

  const fractionalPrice = { packing: { problem: {
    sheets: [{ ...sheetStock, cost: 0.1 }],
    demands: [{ ...gridSheet.demands[0], quantity: 1 }],
  } } };
  const costOptions = { objective: 'total_cost' };
  const fractionalCost = api.solve2dOptimized(fractionalPrice, costOptions);
  assert.equal(fractionalCost.solution.total_cost, 0.1);
  check(['exact_cost_2d'], 'non-dyadic sheet price', { problem: fractionalPrice, options: costOptions },
    fractionalCost, false, 'exact binary64 certificate requires nonnegative dyadic amounts ' +
    'with denominator dividing 2^16 and totals at most 2^53 / 2^16');

  const sheetOpen = { problem: { ...gridSheet, sheets: [{ ...sheetStock, width: 7, height: 7 }] } };
  const openSheet = optimize('solve2dOptimized', ['optimized_2d', 'exact_open_2d'],
    { packing: sheetOpen }, 'open_dimension_xy', 'shrinks both sheet axes');
  assert.equal(openSheet.report.primary_value, 18);

  const binOpen = { problem: {
    bins: [{ ...binStock, width: 3, height: 3, depth: 8 }],
    demands: gridBin.demands,
  } };
  const openBin = optimize('solve3dOptimized', ['optimized_3d', 'exact_open_3d'],
    { packing: binOpen }, 'open_dimension_z', 'shrinks bin depth');
  assert.deepEqual(openBin.report.open_extents, [3, 3, 6]);

  const optimizedStaged = optimize('solve2dStagedOptimized', ['optimized_staged_2d'],
    { packing: staged }, 'bin_count', 'preserves physical cut tree');
  assert.equal(optimizedStaged.solution.production_order.length, 2);
  const optimizedLoading = optimize('solve3dLoadingOptimized', ['optimized_loading_3d'],
    { packing: loading }, 'bin_count', 'preserves nesting and axle loads');
  assert.equal(optimizedLoading.solution.layouts[0].stacks[0].items.length, 2);
}

function shape(exterior) {
  return { components: [{ exterior }] };
}

function polygon(points) {
  return shape({ kind: 'polygon', vertices: points.map(([x, y]) => ({ x, y })) });
}

function checkIrregularCases(api, check) {
  const circle = (x, y, radius) => shape({ kind: 'circle', center: { x, y }, radius });
  const rectangle = (w, h) => polygon([[0, 0], [w, 0], [w, h], [0, h]]);
  const source = {
    bins: [{ name: 'disc stock', shape: circle(5, 5, 5), quantity: 1 }],
    demands: [{
      name: 'disc', shape: circle(0, 0, 5), quantity: 1,
      allowed_rotations: [{ start: 0, end: 0 }],
    }],
  };
  const circles = api.solveIrregular(source, {});
  assert.equal(circles.feasible, true);
  check(['irregular_circles'], 'equal circle boundaries', { source, options: {} }, circles);
  const forged = structuredClone(circles);
  forged.layouts[0].placements[0].x += 0.125;
  check(['irregular_circles'], 'forged disc outside stock', { source, options: {} }, forged, false);

  const triangleSource = {
    bins: [{ name: 'panel', shape: rectangle(20, 10), quantity: 1 }],
    demands: [{
      ...source.demands[0], name: 'triangle', shape: polygon([[0, 0], [2, 0], [0, 1]]), quantity: 2,
    }],
  };
  const options = { item_spacing: 0.5, bin_spacing: 0.125 };
  const triangles = api.solveIrregular(triangleSource, options);
  assert.equal(triangles.feasible, true);
  const triangleInput = { source: triangleSource, options };
  check(['irregular_polygons', 'irregular_sloped_cleared'], 'sloped parts with positive spacing',
    triangleInput, triangles);
  const overlap = structuredClone(triangles);
  overlap.layouts[0].placements[1] = overlap.layouts[0].placements[0];
  check(['irregular_sloped_cleared'], 'forged overlapping triangles', triangleInput, overlap, false);

  const coincidentHole = structuredClone(triangleInput);
  const component = coincidentHole.source.demands[0].shape.components[0];
  component.holes = [component.exterior];
  check(['irregular_sloped_cleared'], 'hole identical to its exterior', coincidentHole, triangles, false,
    'polygon hole must lie strictly inside its exterior');

  const tiles = {
    ...triangleSource,
    demands: [{ ...triangleSource.demands[0], name: 'tile', shape: rectangle(2, 1) }],
  };
  const orthogonal = api.solveIrregular(tiles, {});
  assert.equal(orthogonal.feasible, true);
  check(['irregular_orthogonal', 'irregular_sloped'], 'orthogonal tiles with zero spacing',
    { source: tiles, options: {} }, orthogonal);

  const start = { x: -1.5, y: -1 };
  const capsule = shape({ kind: 'curve', start, segments: [
    { kind: 'line', end: { x: 1.5, y: -1 } },
    { kind: 'arc', end: { x: 1.5, y: 1 }, center: { x: 1.5, y: 0 }, clockwise: false },
    { kind: 'line', end: { x: -1.5, y: 1 } },
    { kind: 'arc', end: start, center: { x: -1.5, y: 0 }, clockwise: false },
  ] });
  const curvedSource = {
    ...triangleSource,
    demands: [{ ...triangleSource.demands[0], name: 'capsule', shape: capsule, quantity: 1 }],
  };
  const curved = api.solveIrregular(curvedSource, options);
  assert.equal(curved.feasible, true);
  check(['irregular_envelopes', 'irregular_curved_exact'], 'capsule with curved ends',
    { source: curvedSource, options }, curved);
  return { source, solution: circles };
}

const cases = [];
for (const [backend, api] of backends) {
  function check(dimensions, description, problem, solution, accepted = true, rejection) {
    for (const dimension of dimensions) {
      cases.push({ dimension, label: `${backend} ${description} (${dimension})`, problem, solution, accepted, rejection });
    }
  }

  const barResult = api.solve1d(stock, { algorithm: 'column_generation' });
  assert.equal(barResult.stock_count, 2);
  cases.push({
    dimension: 'optimal_1d', label: `${backend} minimum stock`,
    problem: stock, solution: barResult, accepted: true,
  });

  const freeResult = api.solve1dMinCost(freeStock, {});
  assert.equal(freeResult.stock_count, 1);
  assert.equal(freeResult.total_cost, 0);
  cases.push({
    dimension: 'exact_min_cost_1d', label: `${backend} exact zero-price tie-breaker`,
    problem: freeStock, solution: freeResult, accepted: true,
  });

  cases.push({
    dimension: 'exact_count_2d', label: `${backend} exact sheet count`,
    problem: gridSheet, solution: api.solve2d(gridSheet, {}), accepted: true,
  }, {
    dimension: 'exact_count_3d', label: `${backend} exact bin count`,
    problem: gridBin, solution: api.solve3d(gridBin, {}), accepted: true,
  });

  const sheetResult = api.solve2d(sheet, { algorithm: 'max_rects' });
  assert.equal(sheetResult.layouts[0].placements.length, 2);
  cases.push({
    dimension: '2d', label: `${backend} edge relief and shortage`,
    problem: sheet, solution: sheetResult, accepted: true,
  });

  const stagedResult = api.solve2dStaged(staged, {});
  assert.equal(stagedResult.production_order.length, 2);
  cases.push({
    dimension: 'staged_2d', label: `${backend} staged cutting with omitted defaults`,
    problem: staged, solution: stagedResult, accepted: true,
  });

  const loadingResult = api.solve3dLoading(loading, {});
  assert.equal(loadingResult.layouts[0].stacks[0].items.length, 2);
  cases.push({
    dimension: 'loading_3d', label: `${backend} nested cargo and axle loads`,
    problem: loading, solution: loadingResult, accepted: true,
  });
  const forged = structuredClone(loadingResult);
  forged.layouts[0].payload = 5;
  cases.push({
    dimension: 'loading_3d', label: `${backend} forged payload`,
    problem: loading, solution: forged, accepted: false,
  });

  const exactWeight = {
    problem: {
      bins: [{ name: 'single', width: 1, height: 1, depth: 1, quantity: 1 }],
      demands: [{ name: 'load', width: 1, height: 1, depth: 1, quantity: 1 }],
    },
    item_weights: [Number.MAX_SAFE_INTEGER],
  };
  const weighted = api.solve3dConstrained(exactWeight, { max_states: 0 });
  assert.deepEqual(weighted.bin_weights, [Number.MAX_SAFE_INTEGER]);
  cases.push({
    dimension: 'constrained_3d', label: `${backend} largest safe exact payload`,
    problem: exactWeight, solution: weighted, accepted: true,
  });
  assert.throws(() => api.solve3dConstrained({
    ...exactWeight,
    item_weights: [Number.MAX_SAFE_INTEGER + 1],
  }), /safe integers/);

  check(['1d', 'accounting_1d', 'exact_1d'], 'solve1d with trim and kerf', stock, barResult);
  check(['min_cost_1d'], 'solve1dMinCost zero-price bound', freeStock, freeResult);
  check(['accounting_2d'], 'solve2d edge relief and shortage accounting', sheet, sheetResult);
  const forgedAccounting = { ...sheetResult, total_cost: sheetResult.total_cost + 1 };
  check(['accounting_2d'], 'forged sheet material cost', sheet, forgedAccounting, false);

  const constrainedSheet = {
    problem: {
      sheets: [{ name: 'trimmed', width: 12, height: 8, kerf: 1, quantity: 1 }],
      demands: [4, 3].map(width => ({ name: 'panel', width, height: 6, quantity: 1, can_rotate: false })),
    },
    constraints: [{ trim_top: 1, trim_bottom: 1, trim_left: 1, trim_right: 1,
      defects: [{ x: 6, y: 1, width: 1, height: 6 }] }],
  };
  const constrained = api.solve2dConstrained(constrainedSheet, {});
  assert.deepEqual(constrained.solution.unplaced, []);
  check(['constrained_2d'], 'indexed sheet with trims, a defect, and duplicate labels',
    constrainedSheet, constrained);

  const adaptive = api.solve2dAdaptive(gridSheet, { max_candidates: 4 });
  assert.equal(adaptive.count_optimal, true);
  check(['2d', 'accounting_2d'], 'solve2dAdaptive attains geometric count bound', gridSheet, adaptive.solution);
  const sheetBound = api.lowerBound2d(gridSheet);
  const [{ width, height, quantity }] = gridSheet.demands;
  const [{ width: sheetWidth, height: sheetHeight }] = gridSheet.sheets;
  assert.equal(Math.ceil(width * height * quantity / (sheetWidth * sheetHeight)), 1);
  assert.equal(sheetBound, 2);
  assert.equal(adaptive.lower_bound, sheetBound);
  check(['lower_bound_2d'], 'DFF bound exceeds area bound', gridSheet, sheetBound);
  check(['lower_bound_2d'], 'forged inflated sheet bound', gridSheet, sheetBound + 1, false);

  const boxOptions = { algorithm: 'branch_and_bound' };
  const boxes = api.solve3d(gridBin, boxOptions);
  assert.equal(boxes.bin_count, 2);
  check(['3d', 'accounting_3d'], 'solve3d branch-and-bound packing', gridBin, boxes);
  check(['lower_bound_3d'], 'solve3d geometric count bound', gridBin, boxes.lower_bound);
  const fullBin = {
    ...gridBin, demands: [{ ...gridBin.demands[0], width: 5, height: 5, depth: 5 }],
  };
  check(['optimal_3d'], 'solve3d attains the volume bound', fullBin, api.solve3d(fullBin, {}));

  const barPlanOptions = { preset: 'chop_saw', fence_reset_cost: 0.5 };
  const barPlan = api.plan1dCuts(stock, barResult, barPlanOptions);
  check(['cut_plan_1d'], 'chop saw with kerf and a remnant',
    { problem: stock, solution: barResult, options: barPlanOptions }, barPlan);

  const sawProblem = staged.packing.problem;
  const sawPacking = api.solve2d(sawProblem, { algorithm: 'guillotine' });
  assert.equal(sawPacking.layouts[0].placements.length, 2);
  check(['optimal_2d'], 'solve2d attains the area bound', sawProblem, sawPacking);
  for (const options of [
    { preset: 'table_saw', fence_reset_cost: 0.5 },
    { preset: 'cnc_router', tool_up_down_cost: 0.25, travel_cost: 0.125 },
  ]) {
    const { preset } = options;
    const plan = api.plan2dCuts(sawPacking, options);
    const input = { solution: sawPacking, options };
    assert.ok(plan.sheet_plans[0].num_cuts > 0);
    check(['cut_plan_2d'], `plan2dCuts ${preset}`, input, plan);
    if (preset === 'cnc_router') {
      const forgedPlan = structuredClone(plan);
      forgedPlan.sheet_plans[0].steps.pop();
      check(['cut_plan_2d'], 'forged CNC tool path', input, forgedPlan, false);
    }
  }
  const job = {
    problem: sawProblem, layouts: stagedResult.solution.layouts,
    stock_indices: stagedResult.stock_indices, demand_indices: stagedResult.demand_indices,
  };
  const sawOptions = { machine: 'table_saw' };
  const sawPlan = api.plan2dSawCuts(job, sawOptions);
  assert.equal(sawPlan.counts.cuts, 1);
  check(['saw_plan'], 'workpiece-aware saw schedule from staged packing', { job, options: sawOptions }, sawPlan);

  checkOptimizationCases(api, check);
  const irregular = checkIrregularCases(api, check);

  for (const [dimension, method, problem, error] of [
    ['1d', 'solve1d', { ...stock, demands: [{ ...stock.demands[0], length: 12 }] }, /no feasible stock/],
    ['2d', 'solve2d', { ...gridSheet, demands: [{ ...gridSheet.demands[0], width: 6 }] }, /no feasible sheet/],
    ['3d', 'solve3d', { ...gridBin, demands: [{ ...gridBin.demands[0], depth: 6 }] }, /no feasible bin/],
  ]) {
    assert.throws(() => api[method](problem, {}), { name: 'Error', message: error }, `${backend} ${method}`);
    // The binding throws for oversize parts. Lean independently checks the reason against the source.
    const input = dimension === '1d' ? problem : { problem };
    check([`infeasible_${dimension}`], `${method} oversize witness`, input, { witness: 'oversize' });
  }
  const withStock = fields => ({ ...stock, stock: [{ ...stock.stock[0], ...fields }] });
  assert.throws(() => api.solve1d(withStock({ length: 0 })), /must have a positive length/);
  assert.throws(() => api.solve1d(withStock({ cost: NaN })), /numeric input fields must be finite/);
  assert.throws(() => api.solve1dMinCost(withStock({ cost: -1 })), /finite non-negative cost/);
  assert.throws(() => api.solve1dOptimized({ packing: stock }, { unexpected_option: true }),
    /unknown field `unexpected_option`/);

  if (backend === 'Node') {
    const options = { algorithm: 'column_generation' };
    check(['1d'], 'solve1D alias', stock, api.solve1D(stock, options));
    check(['2d'], 'solve2D alias', sheet, api.solve2D(sheet, { algorithm: 'max_rects' }));
    check(['3d'], 'solve3D alias', gridBin, api.solve3D(gridBin, boxOptions));
    check(['cut_plan_1d'], 'plan1d_cuts alias', { problem: stock, solution: barResult, options: barPlanOptions },
      api.plan1d_cuts(stock, barResult, barPlanOptions));
    check(['cut_plan_2d'], 'plan2d_cuts alias', { solution: sawPacking, options: {} }, api.plan2d_cuts(sawPacking));
    assert.equal(api.version(), require('../node/package.json').version);
  } else {
    for (const [dimension, method, problem, options, expected] of [
      ['1d', 'solve1dJson', stock, { algorithm: 'column_generation' }, barResult],
      ['2d', 'solve2dJson', sheet, { algorithm: 'max_rects' }, sheetResult],
      ['3d', 'solve3dJson', gridBin, boxOptions, boxes],
      ['irregular_circles', 'solveIrregularJson', irregular.source, {}, irregular.solution],
    ]) {
      const solution = JSON.parse(api[method](JSON.stringify(problem), JSON.stringify(options)));
      assert.deepEqual(solution, expected, `${backend} ${method} agrees with the object API`);
      const input = method === 'solveIrregularJson' ? { source: problem, options } : problem;
      check([dimension], method, input, solution);
    }
    assert.equal(api.version(), require('../wasm/package.json').version);
  }
}

const wire = JSON.stringify(cases);
for (const [index, roundTripped] of JSON.parse(wire).entries()) {
  const { label, solution } = cases[index];
  assert.deepEqual(roundTripped.solution, solution, `${label} survives JSON round-trip`);
}
process.stdout.write(wire);
