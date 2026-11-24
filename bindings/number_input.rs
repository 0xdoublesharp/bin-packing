//! Exact integer checks shared by the Node and WASM loading boundaries.

use bin_packing::three_d::constrained::ConstrainedProblem3D;
use bin_packing::three_d::loading::{LoadingProblem3D, LoadingSolution3D};

const UNSAFE_INTEGER: &str =
    "weights and loading limits must be nonnegative JavaScript safe integers";
const PAYLOAD_OVERFLOW: &str = "bin payload exceeds JavaScript safe integers";

fn is_safe_js_integer(value: u64) -> bool {
    value <= 9_007_199_254_740_991 // Number.MAX_SAFE_INTEGER
}

fn is_safe_js_sum(acc: u64, weight: u64) -> bool {
    acc as u128 + weight as u128 <= 9_007_199_254_740_991
}

fn safe(values: impl IntoIterator<Item = u64>) -> Result<(), &'static str> {
    if !values.into_iter().all(is_safe_js_integer) {
        return Err(UNSAFE_INTEGER);
    }
    Ok(())
}

pub(crate) fn weights(problem: &ConstrainedProblem3D) -> Result<(), &'static str> {
    safe(
        problem
            .item_weights
            .iter()
            .copied()
            .chain(problem.bin_max_weights.iter().flatten().copied()),
    )
}

pub(crate) fn loading(problem: &LoadingProblem3D) -> Result<(), &'static str> {
    weights(&problem.packing)?;
    safe(problem.item_rules.iter().filter_map(|rule| rule.maximum_weight_above))?;
    for rule in &problem.bin_rules {
        if let Some(density) = rule.maximum_stack_density {
            safe([density.numerator, density.denominator])?;
        }
        if let Some(axles) = rule.axle_limits {
            safe([axles.front_maximum, axles.rear_maximum, axles.front_tare, axles.rear_tare])?;
        }
    }
    Ok(())
}

pub(crate) fn payloads(values: &[u64]) -> Result<(), &'static str> {
    safe(values.iter().copied())
}

pub(crate) fn indexed_payloads(
    weights: &[u64],
    indices: &[Vec<usize>],
) -> Result<(), &'static str> {
    let weight_at = |index| {
        if weights.is_empty() {
            Ok(0)
        } else {
            weights.get(index).copied().ok_or("invalid indexed loading source")
        }
    };
    for layout in indices {
        let Some((&last, prefix)) = layout.split_last() else {
            continue;
        };
        let mut payload = 0u64;
        for &index in prefix {
            payload = payload.checked_add(weight_at(index)?).ok_or(PAYLOAD_OVERFLOW)?;
        }
        let weight = weight_at(last)?;
        // Check the final sum before exposing the payload to JavaScript.
        if !is_safe_js_sum(payload, weight) {
            return Err(if payload.checked_add(weight).is_some() {
                UNSAFE_INTEGER
            } else {
                PAYLOAD_OVERFLOW
            });
        }
    }
    Ok(())
}

pub(crate) fn loaded(solution: &LoadingSolution3D) -> Result<(), &'static str> {
    for layout in &solution.layouts {
        safe([layout.payload])?;
        safe(layout.stacks.iter().map(|stack| stack.weight))?;
        if let Some(axles) = layout.axle_loads {
            safe([axles.front, axles.rear])?;
        }
    }
    Ok(())
}
