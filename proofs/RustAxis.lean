import Packing
import GeneratedRustAxis

set_option warningAsError true

namespace Packing.RustAxis

def AxisEnd (start extent gap limit : BitVec 32) : Prop :=
  start.toNat + extent.toNat + gap.toNat ≤ limit.toNat

instance (start extent gap limit : BitVec 32) : Decidable (AxisEnd start extent gap limit) := by
  unfold AxisEnd
  infer_instance

private theorem sums_fit_u64 (start extent gap : BitVec 32) :
    start.toNat + extent.toNat < 2^64 ∧ start.toNat + extent.toNat + gap.toNat < 2^64 := by
  have startBound := start.isLt
  have extentBound := extent.isLt
  have gapBound := gap.isLt
  exact ⟨by omega, by omega⟩

/-- The checked compiler output returns the exact natural-number decision without panicking. -/
theorem checked_refines (start extent gap limit : BitVec 32) :
    GeneratedRustAxis.checked start extent gap limit =
      some (decide (AxisEnd start extent gap limit)) := by
  obtain ⟨first, second⟩ := sums_fit_u64 start extent gap
  simp [GeneratedRustAxis.checked, AxisEnd, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second,
    Nat.not_le_of_lt first, Nat.not_le_of_lt second]

/-- The optimized compiler output makes the same decision for every u32 input. -/
theorem optimized_refines (start extent gap limit : BitVec 32) :
    GeneratedRustAxis.optimized start extent gap limit =
      some (decide (AxisEnd start extent gap limit)) := by
  obtain ⟨first, second⟩ := sums_fit_u64 start extent gap
  simp [GeneratedRustAxis.optimized, AxisEnd, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second]

theorem optimized_accepts (start extent gap limit : BitVec 32) :
    GeneratedRustAxis.optimized start extent gap limit = some true ↔
      start.toNat + extent.toNat + gap.toNat ≤ limit.toNat := by
  simp [optimized_refines, AxisEnd]

theorem bounded_axis_cell {start extent limit : BitVec 32} {cell : Nat}
    (h : GeneratedRustAxis.optimized start extent 0 limit = some true)
    (hcell : cell < start.toNat + extent.toNat) : cell < limit.toNat := by
  have hfit := (optimized_accepts start extent 0 limit).mp h
  omega

/-- The comparison used to admit a 1D cut is the contract for appending that cut. -/
theorem append_fits (cuts : List Nat) (kerf : Nat) (used length gap capacity : BitVec 32)
    (oldLength : used.toNat = linearLength kerf cuts)
    (spacing : gap.toNat = (if cuts.isEmpty then 0 else kerf)) :
    GeneratedRustAxis.optimized used length gap capacity = some true ↔
      linearLength kerf (cuts ++ [length.toNat]) ≤ capacity.toNat := by
  rw [optimized_accepts, oldLength, spacing, linearLength_append]

/-- Two directional comparisons implement the existing one-axis kerf specification. -/
theorem pairwise_gap (a sizeA b sizeB gap : BitVec 32) :
    (GeneratedRustAxis.optimized a sizeA gap b = some true ∨
      GeneratedRustAxis.optimized b sizeB gap a = some true) ↔
      AxisSeparated gap.toNat a.toNat sizeA.toNat b.toNat sizeB.toNat := by
  simp [optimized_accepts, AxisSeparated]

end Packing.RustAxis

open Lean

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
    throwError "no local RustAxis theorems audited"
