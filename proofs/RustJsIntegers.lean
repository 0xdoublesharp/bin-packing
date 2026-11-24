import GeneratedJsIntegers

set_option warningAsError true

namespace Packing.RustJsIntegers

theorem node_refines (value : BitVec 64) :
    GeneratedJsIntegers.node value = some (decide (value.toNat < 2^53)) := by
  have h : (value.toNat ≤ 9007199254740991) ↔ value.toNat < 2^53 := by omega
  simp [GeneratedJsIntegers.node, h]

theorem wasm_refines (value : BitVec 64) :
    GeneratedJsIntegers.wasm value = some (decide (value.toNat < 2^53)) := by
  have h : (value.toNat ≤ 9007199254740991) ↔ value.toNat < 2^53 := by omega
  simp [GeneratedJsIntegers.wasm, h]

theorem accepted_uses_no_more_than_53_bits {value : BitVec 64}
    (accepted : GeneratedJsIntegers.node value = some true ∨
      GeneratedJsIntegers.wasm value = some true) :
    (BitVec.ofNat 53 value.toNat).toNat = value.toNat := by
  have bound : value.toNat < 2^53 := by
    simpa [node_refines, wasm_refines] using accepted
  simp [Nat.mod_eq_of_lt bound]

private theorem sum_fits_u128 (acc weight : BitVec 64) :
    acc.toNat + weight.toNat < 2^128 := by
  have := acc.isLt
  have := weight.isLt
  omega

private theorem sum_safe_iff (acc weight : BitVec 64) :
    acc.toNat + weight.toNat ≤ 9007199254740991 ↔ acc.toNat + weight.toNat < 2^53 := by
  omega

theorem node_dev_sum_refines (acc weight : BitVec 64) :
    GeneratedJsIntegers.node_dev_sum acc weight = some (decide (acc.toNat + weight.toNat < 2^53)) := by
  have bound := sum_fits_u128 acc weight
  simp [GeneratedJsIntegers.node_dev_sum, Nat.not_le_of_lt bound, Nat.mod_eq_of_lt bound,
    sum_safe_iff]

theorem node_release_sum_refines (acc weight : BitVec 64) :
    GeneratedJsIntegers.node_release_sum acc weight =
      some (decide (acc.toNat + weight.toNat < 2^53)) := by
  simp [GeneratedJsIntegers.node_release_sum, Nat.mod_eq_of_lt (sum_fits_u128 acc weight),
    sum_safe_iff]

theorem wasm_dev_sum_refines (acc weight : BitVec 64) :
    GeneratedJsIntegers.wasm_dev_sum acc weight = some (decide (acc.toNat + weight.toNat < 2^53)) := by
  have bound := sum_fits_u128 acc weight
  simp [GeneratedJsIntegers.wasm_dev_sum, Nat.not_le_of_lt bound, Nat.mod_eq_of_lt bound,
    sum_safe_iff]

theorem wasm_release_sum_refines (acc weight : BitVec 64) :
    GeneratedJsIntegers.wasm_release_sum acc weight =
      some (decide (acc.toNat + weight.toNat < 2^53)) := by
  simp [GeneratedJsIntegers.wasm_release_sum, Nat.mod_eq_of_lt (sum_fits_u128 acc weight),
    sum_safe_iff]

theorem accepted_sum_fits_u64 {acc weight : BitVec 64}
    (accepted : GeneratedJsIntegers.node_dev_sum acc weight = some true ∨
      GeneratedJsIntegers.node_release_sum acc weight = some true ∨
      GeneratedJsIntegers.wasm_dev_sum acc weight = some true ∨
      GeneratedJsIntegers.wasm_release_sum acc weight = some true) :
    acc.toNat + weight.toNat < 2^64 := by
  have bound : acc.toNat + weight.toNat < 2^53 := by
    simpa [node_dev_sum_refines, node_release_sum_refines, wasm_dev_sum_refines,
      wasm_release_sum_refines] using accepted
  omega

end Packing.RustJsIntegers

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
    throwError "no local RustJsIntegers theorems audited"
