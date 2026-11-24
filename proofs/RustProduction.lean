import GeneratedRustProduction

set_option warningAsError true

namespace Packing.RustProduction

open GeneratedRustProduction

/-- Kerf relief expands an axis up to the largest coordinate. -/
def effectiveBound (extent kerf : Nat) (relief : Bool) : Nat :=
  if relief then min (2^32 - 1) (extent + kerf) else extent

/-- A trimmed interval must start after the leading trim and end before the trailing trim. -/
def trimmedAxis (start extent trimLow trimHigh stock : Nat) : Prop :=
  trimLow ≤ start ∧ start + extent + trimHigh ≤ stock

instance (start extent trimLow trimHigh stock : Nat) :
    Decidable (trimmedAxis start extent trimLow trimHigh stock) := by
  unfold trimmedAxis
  infer_instance

/-- The integer threshold scale used by the geometric lower bound. -/
def thresholdScale (length threshold capacity : Nat) : Nat :=
  if length < threshold then 0
  else if capacity - threshold < length then capacity
  else length

private theorem widened_sums (start extent trimHigh : BitVec 32) :
    start.toNat + extent.toNat < 2^64 ∧ start.toNat + extent.toNat + trimHigh.toNat < 2^64 := by
  have := start.isLt
  have := extent.isLt
  have := trimHigh.isLt
  exact ⟨by omega, by omega⟩

private theorem widened_product (width height : BitVec 32) :
    width.toNat * height.toNat < 2^64 := by
  have h := Nat.mul_le_mul
    (show width.toNat ≤ 2^32 - 1 from by have := width.isLt; omega)
    (show height.toNat ≤ 2^32 - 1 from by have := height.isLt; omega)
  exact Nat.lt_of_le_of_lt h (by decide)

theorem effective_axis_bound_checked_refines (extent kerf : BitVec 32) (relief : Bool) :
    effective_axis_bound_checked extent kerf relief =
      some (effectiveBound extent.toNat kerf.toNat relief) := by
  cases relief <;> rfl

theorem effective_axis_bound_optimized_refines (extent kerf : BitVec 32) (relief : Bool) :
    effective_axis_bound_optimized extent kerf relief =
      some (effectiveBound extent.toNat kerf.toNat relief) := by
  cases relief <;> rfl

theorem fits_trimmed_axis_checked_refines (start extent trimLow trimHigh stock : BitVec 32) :
    fits_trimmed_axis_checked start extent trimLow trimHigh stock =
      some (decide (trimmedAxis start.toNat extent.toNat trimLow.toNat trimHigh.toNat stock.toNat)) := by
  obtain ⟨first, second⟩ := widened_sums start extent trimHigh
  by_cases h : trimLow.toNat ≤ start.toNat <;>
    simp [fits_trimmed_axis_checked, trimmedAxis, h, Nat.mod_eq_of_lt first,
      Nat.mod_eq_of_lt second, Nat.not_le_of_lt first, Nat.not_le_of_lt second]

theorem fits_trimmed_axis_optimized_refines (start extent trimLow trimHigh stock : BitVec 32) :
    fits_trimmed_axis_optimized start extent trimLow trimHigh stock =
      some (decide (trimmedAxis start.toNat extent.toNat trimLow.toNat trimHigh.toNat stock.toNat)) := by
  obtain ⟨first, second⟩ := widened_sums start extent trimHigh
  by_cases h : trimLow.toNat ≤ start.toNat <;>
    simp [fits_trimmed_axis_optimized, trimmedAxis, h, Nat.mod_eq_of_lt first,
      Nat.mod_eq_of_lt second]

theorem area_u64_checked_refines (width height : BitVec 32) :
    area_u64_checked width height = some (width.toNat * height.toNat) := by
  have bound := widened_product width height
  simp [area_u64_checked, Nat.not_le_of_lt bound, Nat.mod_eq_of_lt bound]

theorem area_u64_optimized_refines (width height : BitVec 32) :
    area_u64_optimized width height = some (width.toNat * height.toNat) := by
  simp [area_u64_optimized, Nat.mod_eq_of_lt (widened_product width height)]

theorem scale_threshold_checked_refines (length threshold capacity : BitVec 32)
    (h : threshold.toNat ≤ capacity.toNat) :
    scale_threshold_checked length threshold capacity =
      some (thresholdScale length.toNat threshold.toNat capacity.toNat) := by
  by_cases small : length.toNat < threshold.toNat <;>
    simp [scale_threshold_checked, thresholdScale, small, Nat.not_lt_of_ge h]
  split <;> rfl

theorem scale_threshold_optimized_refines (length threshold capacity : BitVec 32)
    (h : threshold.toNat ≤ capacity.toNat) :
    scale_threshold_optimized length threshold capacity =
      some (thresholdScale length.toNat threshold.toNat capacity.toNat) := by
  by_cases small : length.toNat < threshold.toNat <;>
    simp [scale_threshold_optimized, thresholdScale, small, Nat.not_lt_of_ge h]
  split <;> rfl

theorem scale_floor_checked_refines (length divisor : BitVec 32) (h : 0 < divisor.toNat) :
    scale_floor_checked length divisor = some (length.toNat / divisor.toNat) := by
  simp [scale_floor_checked, Nat.ne_of_gt h]

theorem scale_floor_optimized_refines (length divisor : BitVec 32) (h : 0 < divisor.toNat) :
    scale_floor_optimized length divisor = some (length.toNat / divisor.toNat) := by
  simp [scale_floor_optimized, Nat.ne_of_gt h]

theorem scale_floor_rejects_zero (length : BitVec 32) :
    scale_floor_checked length 0 = none ∧ scale_floor_optimized length 0 = none := by
  simp [scale_floor_checked, scale_floor_optimized]

theorem scale_threshold_checked_rejects_underflow (length threshold capacity : BitVec 32)
    (h : capacity.toNat < threshold.toNat) (large : threshold.toNat ≤ length.toNat) :
    scale_threshold_checked length threshold capacity = none := by
  simp [scale_threshold_checked, h, Nat.not_lt_of_ge large]

end Packing.RustProduction

open Lean Packing.RustProduction

run_cmd do
  let env ← getEnv
  let standard := [`propext, `Quot.sound, `Classical.choice]
  let mut audited := 0
  for (name, info) in env.constants.toList do
    if !env.isImportedConst name then
      if info.isAxiom then
        throwError "unexpected local axiom {name}"
      if info.isTheorem then
        for dependency in ← Lean.collectAxioms name do
          unless standard.contains dependency do
            throwError "unexpected axiom {dependency} in {name}"
        audited := audited + 1
  if audited == 0 then
    throwError "no local RustProduction theorems audited"
