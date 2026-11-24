# Correctness checks and production coverage

Run `./scripts/check-quality.sh` for the required Rust/Python test, formatting,
metadata, Clippy and documentation gate. `./scripts/check-features.sh` checks
isolated feature combinations; `./scripts/check-bindings.sh` builds and checks
the native and WebAssembly packages, declarations, documented JavaScript examples
and actual browser entry points. The quality gate also verifies source-derived
[reference facts](reference.md), local links and complete Rust examples; see
[documentation maintenance](documentation.md).

The tests include independent geometry, inventory and physical constraint checks:

- Analytic circular/arc areas and 324 exact-circle clearance cases, strict hole
  containment, source transforms and corrupted irregular certificates.
- 72 physical strip tilings, 54 stricter cut-limit rejections, cut-tree
  conservation and invalid source/tree references.
- Hand-calculated axle reactions, density/payload/stack boundaries, nested-floor
  bounds and forged loading metadata.
- Small finite knapsack oracles, mandatory demand accounting, objective changes,
  cropped defects/trims and fixed axle positions after cropping.
- A fixed-seed set of 64 generated jobs across 28 separate 3D strategies. Every
  result must place an item, respect finite stock and the single allowed source
  rotation, conserve quantities, stay within bounds and avoid overlap. Existing
  1D/2D property tests also use a fixed seed.

## Lean verification

Run `./scripts/check-proofs.sh` with [Elan](https://lean-lang.org/install/manual/)
installed. The check uses the pinned [Lean toolchain](../proofs/lean-toolchain)
and requires no Mathlib dependencies. It is an opt-in companion to the quality
gate. The verifier audits the named guarantees for axioms beyond Lean's
standard foundations.

| Proof module | Checks backed by the model |
| --- | --- |
| [Packing](../proofs/Packing.lean) | Effective stock bounds, non-overlap, kerf, source dimensions and orientations, finite stock, per-demand totals, and 1D cut-length accounting. |
| [Indexed](../proofs/Indexed.lean) | Source provenance with repeated labels, per-row shortages, sheet trims and defect clearance, and 3D payload reconstructed from source weights. |
| [Staged](../proofs/Staged.lean) | Exact full-span children and conservation of material, blade clearance, strip and stage rules, production order, and kerf and waste totals. |
| [Saw](../proofs/Saw.lean) | Operation order, live workpieces, active setup and orientation, exact child geometry and material conservation, and finished-part readback. |
| [Loading](../proofs/Loading.lean) | Nesting and final top height, footprint, density, weight above each item, payload, unloading order, exact axle reactions, and their integer ceilings. |
| [Circles](../proofs/Circles.lean) | Containment and disjoint interiors in the exact scaled-coordinate model, source transforms, circular holes and defects, and spacing. |
| [Polygons](../proofs/Polygons.lean) | Rectangular stock containment and separating projections for conservative hulls of straight and curved contours, with a proved enclosing bound for circular arcs. |
| [Orthogonal](../proofs/Orthogonal.lean) | Even–odd crossing strips reconstruct material with axis-aligned edges, including concavities and holes. Tile clearance proves disjoint material. |
| [Sloped](../proofs/Sloped.lean) | Exact cross-multiplication checks the ordering and separation of sloped strip edges at zero clearance, including concave polygons and holes. |
| [IrregularExact](../proofs/IrregularExact.lean) | Exact sloped-tile and disc-to-segment clearance, distance preservation under exact rotations, error margins for approximate rotations, and conservative chord-slab bounds for minor arcs. |
| [Optimality](../proofs/Optimality.lean) | Padded length, effective area, or volume can certify minimum count for complete single-stock-type packings. A tight price-per-usable-length bound can certify minimum 1D material cost across stock types with integral prices. |
| [ExactLinear](../proofs/ExactLinear.lean) | Exhaustive allocation proves attainability and excludes better count-first or cost-first scores with finite inventory and unplaced cuts. |
| [ExactGrid](../proofs/ExactGrid.lean) | Exhaustive integer-grid placement excludes complete packings with fewer sheets or bins under source, orientation, and kerf constraints. |
| [Bounds](../proofs/Bounds.lean) | Floor and threshold scales preserve one-axis capacity. Transformed layouts give sound lower bounds for complete 2D and 3D packings under the modeled stock and rotation conditions. |
| [Optimization](../proofs/Optimization.lean) | Objective ranking and bounds, source-indexed optimized result checks, and sound bounded exact witnesses for knapsack, grid cost, open dimensions, and infeasibility. |
| [Reuse](../proofs/Reuse.lean) | Recoverable offcuts are live terminal saw workpieces distinct from finished parts, within their source sheet and clear of parts and other offcuts. Forecast placements are valid and disjoint, with checked fulfillment counts, area, and value. |
| [CutPlan](../proofs/CutPlan.lean) | Bar replay preserves length and operation counts. Sheet checks replay legacy saw cuts or CNC tool state and outlines within physical stock bounds, and recompute operation costs. |
| [AccountingAndSemantics](../proofs/AccountingAndSemantics.lean) | Modeled input validation and defaults, material and price accounting, production groups and stages, saw replay conservation, loading constraints, and bounded search termination and budget rules. |

The [Rust integration test](../crates/bin-packing/tests/lean_certificates.rs)
feeds serialized original inputs and solver outputs to Lean. It exercises every
algorithm selectable through `solve_1d`, `solve_2d`, and `solve_3d`, as well as
specialized entry points, and tests rejection of deliberately corrupted results.
`./scripts/check-proofs.sh --bindings` tests the built native Node and
Node-target WebAssembly packages on disk and independently proves MIR from the
current checkout. For release attestation, rebuild both packages from that
checkout with `./scripts/check-bindings.sh` before running the binding proof check.

### Prove production arithmetic

The proof command emits Rust MIR in both development and release profiles for
six production functions. The [restricted translator](../scripts/check-rust-proofs.py)
rejects unsupported instructions and control flow. Lean proves the translated
functions refine the following arithmetic contracts.

| Rust function | Proved contract |
| --- | --- |
| `end_with_gap_at_most` | For all `u32` inputs, accepts exactly when `start + extent + gap ≤ limit`. The checked additions cannot overflow. Consequences cover 1D cut admission, bounded axis cells, and pairwise kerf separation. |
| `effective_axis_bound` | Returns the unchanged extent with edge relief disabled, or the extent plus kerf saturated at `u32::MAX` with relief enabled. |
| `fits_trimmed_axis` | Accepts exactly when the start clears the leading trim and the end plus trailing trim fits the stock. The widened additions cannot overflow. |
| `area_u64` | Returns the exact product of two `u32` dimensions in `u64`. |
| `scale_threshold` | Given a threshold at most capacity, returns zero below the threshold, capacity above `capacity - threshold`, and the original length otherwise. The checked model takes an underflow exit for an invalid threshold if it reaches the subtraction. |
| `scale_floor` | Returns integer floor division for a positive divisor. Both translated profiles take the failure exit for a zero divisor. |

See [RustAxis](../proofs/RustAxis.lean) for the axis-end predicate and its
consequences, and [RustProduction](../proofs/RustProduction.lean) for the other
five functions.

The binding check extracts `is_safe_js_integer` from native Node and
`wasm32-unknown-unknown` release builds and `is_safe_js_sum` from both development
and release builds for each target. The first accepts exactly the `u64` values
below `2^53`. The second accepts exactly when the sum of two `u64` inputs is
below `2^53`. Its widened addition cannot overflow, and any accepted sum fits
in `u64`. See the [production guards](../bindings/number_input.rs) and
[RustJsIntegers](../proofs/RustJsIntegers.lean).

The default proof run includes `python3 -B scripts/check-rust-proofs.py --audit-tcb`.
The audit normalizes guillemets around escaped Lean identifiers when scanning
for proof escapes such as `sorry`, `admit`, `axiom`, `native_decide`, and `unsafe`.
Its `set_option` allowlist permits only one file-wide `set_option warningAsError true`
per source file and rejects `debug.skipKernelTC` and `warningAsError false`.
It rebuilds the proof modules with `-DwarningAsError=true -Ddebug.skipKernelTC=false`
and audits every local theorem in the resulting Lean environment, including the
checker module. The audit rejects local axiom declarations and theorem dependencies
outside `propext`, `Quot.sound`, and `Classical.choice`.

The audit verifies that the active Rust and Lean versions match their exact pins.
It prints SHA-256 digests of `Cargo.lock`, `bindings/node/pnpm-lock.yaml`, and
`bindings/wasm/pnpm-lock.yaml` for release attestation. Any comparison against
reference hashes is a separate attestation step.

### Verify a specific result

`./scripts/check-proofs.sh --verify` reads one JSON object from standard input
and succeeds only when the selected checker accepts it. Use the original job
and the returned solution as JSON. Omitted source fields use the modeled Serde
defaults.

The `optimized_*`, `exact_knapsack_*`, `exact_cost_*`, `reuse_*`, and
`cut_plan_*` checks restrict the prices, profits, weights, and costs they check
to exact nonnegative dyadic values on the `2^-16` grid, with scaled totals at
most `2^53`. The checked arithmetic agrees exactly with Rust's IEEE 754
binary64 arithmetic on this domain. The checkers reject non-dyadic values such
as `0.1`. For cut-plan presets with non-dyadic defaults such as `0.3`, `0.2`, or
`0.01`, supply explicit dyadic overrides in `problem.options`.

- Set `dimension` to `"1d"`, `"2d"`, or `"3d"` with `problem` and `solution`.
  Ordinary packing uses unique demand names to identify source rows.
- Use `"optimal_1d"`, `"optimal_2d"`, or `"optimal_3d"` with the same inputs
  for the single-stock capacity witness. The witness may be inconclusive on an
  optimal result when the capacity bound is weak.
- Use `"min_cost_1d"` for the multi-stock material-price witness. Stock prices
  and the reported total must be exact nonnegative integers at most `2^53`.
- Use `"exact_1d"` or `"exact_min_cost_1d"` to check the full numerical
  count-first or cost-first objective independently of the solver's `exact`
  flag. Both rank fewer unplaced cuts first. Subsequent criteria are bar count,
  waste, and cost for count-first, or cost, bar count, and waste for cost-first.
  Jobs need unique demand names, at most 64 cuts, and at most 65,536 possible
  assignments, including the option to leave a cut unplaced. The total price of
  the modeled stock slots must fit within `2^53` in exact nonnegative integers.
- Use `"exact_count_2d"` or `"exact_count_3d"` for minimum sheet or bin count
  with complete fulfillment and unique demand names. The checker enumerates all
  grid positions and permitted orientations on stock slots that could be used
  in a cheaper plan. It admits at most 64 items, 65,536 stock cells, and an
  upper bound of 65,536 combinations of cells and orientations.
- Use `"lower_bound_2d"` with the numeric return value of the 2D lower-bound
  API, or `"lower_bound_3d"` with the value of the solution's `lower_bound`
  field. Put that number in `solution`. The 3D checker covers one unlimited
  stock type with each demand restricted to the original orientation.
- Use `"optimized_1d"`, `"optimized_2d"`, `"optimized_3d"`,
  `"optimized_staged_2d"`, or `"optimized_loading_3d"` for source-indexed packing,
  the effective problem, and the reported objective value and bound. Put the
  optimizer input in `problem.problem` and its options in `problem.options`.
  A reported primary optimum must meet the objective's fulfillment requirement
  and match the checked bound.
- Use `"exact_knapsack_1d"`, `"exact_knapsack_2d"`, or `"exact_knapsack_3d"` for
  the full knapsack ranking subject to mandatory minima, `"exact_cost_2d"` or
  `"exact_cost_3d"` to exclude cheaper complete grid packings, or `"exact_open_1d"`,
  `"exact_open_2d"`, or `"exact_open_3d"` to certify that the returned packing
  fulfills all demand and attains the minimum open extent or area on a single
  stock type. These tags use the optimizer input and result format above. The
  exact optimizer checks cap search at 128 copies and 65,536 choice combinations.
  The same numeric cap applies to grid cells and candidate crop sizes where
  applicable.
- Use `"infeasible_1d"`, `"infeasible_2d"`, or `"infeasible_3d"` with the
  original packing problem and an `oversize`, `inventory`, or `exhaustive`
  witness in `solution`, either directly or under `solution.witness`. For 2D and
  3D, pass the `ConstrainedProblem2D` or `ConstrainedProblem3D` JSON wrapper
  (`{ "problem": ... }`) as the certificate's `problem`. Oversize and inventory
  witnesses operate on demand and stock rows without expanding quantities.
- Use `"constrained_2d"`, `"constrained_3d"`, `"staged_2d"`, or `"loading_3d"`
  with that entry point's original problem and result.
- For `"saw_plan"`, put the original `job` and `options` inside `problem` and
  the `SawPlan2D` in `solution`.
- For `"cut_plan_1d"` and `"cut_plan_2d"`, put the original packing result and
  planner options in `problem.solution` and `problem.options`. The 1D checker
  also needs the original packing input in `problem.problem`. Put the cut plan
  in `solution`. CNC replay in `"cut_plan_2d"` enforces physical stock bounds
  and rejects paths that overhang the sheet under edge kerf relief.
- For `"reuse_eval_2d"`, put `job`, `forecast`, `options`, and `saw_plan` inside
  `problem`. For `"reuse_solve_2d"`, put the original packing input under `problem.problem`
  with `forecast`, `options`, and the selected job's `saw_plan` alongside it.
  A separate `baseline_job` requires `baseline_saw_plan`. If both baseline fields
  are omitted, the checker uses the selected job and its plan for the baseline.
  Both checkers verify and replay the plans to prove that each recoverable offcut
  is a live terminal workpiece distinct from finished parts. Kerf strips removed
  by the blade fail this check.
- Use `"accounting_1d"`, `"accounting_2d"`, or `"accounting_3d"` with the
  ordinary packing problem and solution to verify material use, waste, and
  source costs, including binary64 accumulation in layout order.
- For `"irregular_circles"`, `"irregular_polygons"`, `"irregular_envelopes"`,
  `"irregular_orthogonal"`, `"irregular_sloped"`, `"irregular_sloped_cleared"`,
  or `"irregular_curved_exact"`, put the nesting input in `problem.source` and
  the options in `problem.options`. The circle and mixed curved checkers support
  circular and rectangular stock. The other checkers use rectangular stock.
  The envelope checker requires matching arc endpoint radii and encloses each
  arc's whole circle. Orthogonal strips support interlocking outlines and
  placements in holes. Sloped strips support zero clearance, and the cleared
  variant adds Euclidean spacing. The sloped, cleared sloped, and mixed curved
  checkers validate simple rings and strict hole containment before constructing
  tiles. The sloped checkers use quarter-turn rotations for off-origin geometry.
  The mixed curved checker handles other rotations with error margins. Its
  outward minor-arc chord slabs and conservative envelopes for other arcs can
  reject a feasible nesting.

### Formal verification scope and trusted base

| Verification area | Proved or checked | Scope limit |
| --- | --- | --- |
| Inputs & public APIs | Modeled validation and JSON defaults, source decoding, and JavaScript integer and sum guards. | Rust and binding integration tests exercise selected end-to-end inputs. |
| Demand & stock accounting | Per-demand placements and shortages, source indices, finite inventory, material use and waste, source costs, and reuse fulfillment. | Each certificate checks the fields and numeric model of its entry point. |
| Packing geometry | Bounds, orientations, kerf, trims, defects, payload, and exact or conservatively enclosed irregular geometry. | Irregular checks use scaled coordinates, supported contour models, and conservative rotation margins where applicable. |
| Physical cutting & loading | Staged tree and saw replay, legacy cut plans, offcut clearance, stack and density limits, unloading paths, and axle reactions. | Guarantees follow the modeled cut, nesting, and unloading rules. |
| Optimization claims | Recomputed bounds and candidate scores, bounded exact optima and infeasibility, and termination and budget rules for the modeled search driver. | Exact checks impose copy, grid, crop, and combination caps. Larger jobs rely on validated certificates and applicable bounds. |
| Execution & release | Lean kernel checks, pinned toolchain checks and lockfile hashes, MIR refinements for the extracted production functions, and Rust, Node, and WASM certificate tests. | Compiler lowering, runtime behavior, and wire mappings outside the extracted functions remain in the trusted base or are exercised by tests. |

The theorems apply to decoded certificates and translated MIR. End-to-end use
trusts the Rust compiler, the MIR translator, the Lean kernel and imports,
the Node and WebAssembly runtimes, and the Serde, N-API, and wasm-bindgen glue.

## Repeat the coverage measurement

Keep disposable output on Scratch. The coverage script uses the configured build
wrapper and a separate instrumented target directory. It needs the pinned nightly
toolchain and its `llvm-tools` component for unstable branch instrumentation;
the library's own toolchain declaration is unchanged.

```sh
python3 -B scripts/check-coverage.py \
  --output-dir /Volumes/Scratch/bin-packing/reports/coverage-new-run \
  --target-dir /Volumes/Scratch/bin-packing/build/coverage \
  --min-lines 96 --min-branches 90
```

Use a fresh output directory for each run. Target artifacts may be reused.
The script reads exact executable paths from Cargo JSON, runs all Rust test
targets with all features and exports profiles with the matching LLVM tools.
It records source hashes, commands, raw profiles, LLVM data, missing lines and
missing branch outcomes. It fails on test failure, missing data, source changes
or a requested minimum that is not met.

The reported percentages count unique LLVM LCOV source lines and branch outcomes
in the production Rust library. Test-only items/modules are excluded using Rust
lexical context, including literals and nested comments. Production code is not
excluded. This is the same counting scope as the initial October 28 measurement.
LLVM's per-function summary uses a different aggregation and remains available in
the raw export. JavaScript/browser execution and doctests are outside this Rust
coverage measurement.

Coverage identifies unexercised paths. Independent oracles and regression tests
provide the behavioral evidence; a percentage alone does not prove correctness.

The [October 28 confidence report](experiments/2026-10-28-confidence.md) records
the first expanded test set and validation repair. The subsequent
[Terra Low batches](experiments/2026-10-28-terra-test-batches.md) record the latest
additional test functions. The later
[existing-test and fault checks](experiments/2026-10-28-branch-proof.md) record
controlled evidence for the expanded cases. The subsequent
[90% branch coverage report](experiments/2026-10-28-branch-90.md) records the
latest measurement and the additional boundary and repair tests.
