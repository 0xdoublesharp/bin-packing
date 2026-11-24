"""The scalar MIR translator must reject unmodeled code and control flow."""

import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location(
    'check_rust_axis', Path(__file__).parents[1] / 'check-rust-proofs.py')
AXIS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AXIS)

# A small synthetic body whose only operation is an unsigned comparison.
COMPARISON = '''
fn end_with_gap_at_most(_1: u32, _2: u32, _3: u32, _4: u32) -> bool {
    let mut _0: bool;
    let _21: u64;
    let _22: u64;

    bb0: {
        StorageLive(_21);
        _21 = copy _4 as u64 (IntToInt);
        _22 = copy _1 as u64 (IntToInt);
        _0 = Le(copy _21, copy _22);
        StorageDead(_21);
        return;
    }
}
'''

CHECKED = '''
fn sample(_1: u64, _2: u64) -> u64 {
    let mut _0: u64;
    let _3: (u64, bool);

    bb0: {
        _3 = AddWithOverflow(copy _1, copy _2);
        assert(!move (_3.1: bool), "arithmetic overflow", copy _1, copy _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = move (_3.0: u64);
        return;
    }
}
'''

DIVISION = '''
fn sample(_1: u32, _2: u32) -> u32 {
    let mut _0: u32;
    let _3: bool;

    bb0: {
        _3 = Eq(copy _2, const 0_u32);
        assert(!move _3, "division by zero", copy _1) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = Div(copy _1, copy _2);
        return;
    }
}
'''

BRANCH = '''
fn sample(_1: bool, _2: u32) -> u32 {
    let mut _0: u32;

    bb0: {
        switchInt(copy _1) -> [0: bb2, otherwise: bb1];
    }
    bb1: {
        _0 = const 4_u32;
        goto -> bb3;
    }
    bb2: {
        _0 = copy _2;
        goto -> bb3;
    }
    bb3: {
        return;
    }
}
'''


def translate_sample(mir, parameters, result):
    return AXIS.translate_mir(mir, 'translated', 'sample', parameters, result)


class RustAxisTranslatorTests(unittest.TestCase):
    def test_comparison_preserves_operand_order_and_strictness(self):
        code = AXIS.translate_mir(COMPARISON, 'sample')
        self.assertIn('let v21 := v4.toNat', code)
        self.assertIn('let v22 := v1.toNat', code)
        self.assertIn('decide (v21 ≤ v22)', code)
        changed = COMPARISON.replace('Le(copy', 'Lt(copy')
        self.assertIn('decide (v21 < v22)', AXIS.translate_mir(changed, 'sample'))

    def test_unmodeled_operation_is_rejected(self):
        changed = COMPARISON.replace('Le(copy', 'Shl(copy')
        with self.assertRaisesRegex(ValueError, 'unsupported MIR expression'):
            AXIS.translate_mir(changed, 'sample')

    def test_dead_or_uninitialized_storage_is_rejected(self):
        changed = COMPARISON.replace('_0 = Le', 'StorageDead(_21);\n        _0 = Le')
        with self.assertRaisesRegex(ValueError, 'expected initialized u64'):
            AXIS.translate_mir(changed, 'sample')

    def test_unmodeled_branch_or_trailing_block_is_rejected(self):
        changed = COMPARISON.replace('return;', 'goto -> bb1;')
        with self.assertRaisesRegex(ValueError, 'unsupported MIR instruction'):
            AXIS.translate_mir(changed, 'sample')
        trailing = COMPARISON.replace('    }\n}', '    }\n    bb1: {\n        return;\n    }\n}')
        with self.assertRaisesRegex(ValueError, 'block outside entry control flow'):
            AXIS.translate_mir(trailing, 'sample')

    def test_numeric_result_models_wrapping(self):
        mir = '''
fn sub(_1: u32, _2: u32) -> u32 {
    let mut _0: u32;
    bb0: {
        _0 = Sub(copy _1, copy _2);
        return;
    }
}
'''
        code = AXIS.translate_mir(mir, 'sample', 'sub', ('u32', 'u32'), 'u32')
        self.assertIn(': Option Nat := do', code)
        self.assertIn('if v1.toNat < v2.toNat then v1.toNat + 2^32 - v2.toNat', code)

    def test_checked_operators_emit_wrapped_values_and_panic_exits(self):
        for operation, value, overflow in (
                ('Add', '(v1.toNat + v2.toNat) % (2^64)', '2^64 ≤ v1.toNat + v2.toNat'),
                ('Mul', '(v1.toNat * v2.toNat) % (2^64)', '2^64 ≤ v1.toNat * v2.toNat'),
                ('Sub', 'v1.toNat + 2^64 - v2.toNat', 'v1.toNat < v2.toNat')):
            with self.subTest(operation=operation):
                code = translate_sample(CHECKED.replace('AddWithOverflow', operation + 'WithOverflow'),
                                        ('u64', 'u64'), 'u64')
                self.assertIn(value, code)
                self.assertIn(f'decide ({overflow})', code)
                self.assertIn('let _ ← if v3.2 then none else some ()', code)
                self.assertIn('let v0 := v3.1', code)
        wasm = CHECKED.replace('unwind continue', 'unwind unreachable')
        self.assertEqual(translate_sample(wasm, ('u64', 'u64'), 'u64'),
                         translate_sample(CHECKED, ('u64', 'u64'), 'u64'))

    def test_malformed_overflow_control_flow_is_rejected(self):
        for modified, error in (
                (CHECKED.replace('!move (_3.1: bool)', 'move (_3.1: bool)'), 'corresponding operation'),
                (CHECKED.replace('copy _1, copy _2) ->', 'copy _2, copy _1) ->'),
                 'corresponding operation'),
                (CHECKED.replace('_3.0: u64', '_3.0: u32'), 'wrong type for MIR projection'),
                (CHECKED.replace('unwind continue', 'unwind: bb1'), 'unsupported MIR instruction')):
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                translate_sample(modified, ('u64', 'u64'), 'u64')

    def test_division_requires_a_dominating_guard_for_the_same_divisor(self):
        code = translate_sample(DIVISION, ('u32', 'u32'), 'u32')
        self.assertIn('let _ ← if v3 then none else some ()', code)
        self.assertIn('let v0 := v1.toNat / v2.toNat', code)
        for modified in (
                DIVISION.replace('Eq(copy _2', 'Eq(copy _1'),
                DIVISION.replace('assert(!move _3, "division by zero", copy _1) -> '
                                 '[success: bb1, unwind continue];', 'goto -> bb1;')):
            with self.subTest(mir=modified), self.assertRaisesRegex(ValueError, 'dominating nonzero guard'):
                translate_sample(modified, ('u32', 'u32'), 'u32')

    def test_diamond_translates_each_predecessor_with_its_own_state(self):
        self.assertIn('if v1 then do\n    let v0 := 4\n    return v0\n'
                      '  else do\n    let v0 := v2.toNat\n    return v0',
                      translate_sample(BRANCH, ('bool', 'u32'), 'u32'))
        inverted = BRANCH.replace('0: bb2, otherwise: bb1', '1: bb2, otherwise: bb1')
        self.assertIn('if v1 then do\n    let v0 := v2.toNat',
                      translate_sample(inverted, ('bool', 'u32'), 'u32'))
        missing = BRANCH.replace('_0 = copy _2;', '')
        with self.assertRaisesRegex(ValueError, 'expected initialized u32 MIR local: _0'):
            translate_sample(missing, ('bool', 'u32'), 'u32')

    def test_unknown_cyclic_and_non_boolean_branches_are_rejected(self):
        for modified, error in (
                (BRANCH.replace('goto -> bb3', 'goto -> bb0'), 'cyclic MIR control flow'),
                (BRANCH.replace('otherwise: bb1', 'otherwise: bb9'), 'target bb9 does not exist'),
                (BRANCH.replace('switchInt(copy _1)', 'switchInt(copy _2)'), 'expected initialized bool'),
                (BRANCH.replace('0: bb2', '2: bb2'), 'unsupported MIR instruction'),
                (BRANCH.replace('goto -> bb3;', 'unreachable;'), 'unsupported MIR instruction')):
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                translate_sample(modified, ('bool', 'u32'), 'u32')

    def test_saturating_and_min_calls_and_unknown_call_rejection(self):
        for callee, args, expected in (
                ('core::num::<impl u32>::saturating_add', 'copy _2, const 1_u32',
                 'min (2^32 - 1) (v2.toNat + 1)'),
                ('std::intrinsics::saturating_add::<u32>', 'copy _2, const 1_u32',
                 'min (2^32 - 1) (v2.toNat + 1)'),
                ('std::cmp::min::<u32>', 'copy _2, const 3_u32', 'min v2.toNat 3'),
                ('<u32 as Ord>::min', 'copy _2, const 3_u32', 'min v2.toNat 3')):
            with self.subTest(callee=callee):
                call = f'_0 = {callee}({args}) -> [return: bb3, unwind continue];'
                changed = BRANCH.replace('_0 = const 4_u32;\n        goto -> bb3;', call)
                self.assertIn('let v0 := ' + expected, translate_sample(changed, ('bool', 'u32'), 'u32'))
                with self.assertRaisesRegex(ValueError, 'unsupported MIR instruction'):
                    translate_sample(changed.replace(callee, 'unrecognized'), ('bool', 'u32'), 'u32')

    def test_integer_and_boolean_operators_remain_typed(self):
        for op, symbol in (('Ge', '≥'), ('Gt', '>'), ('Eq', '='), ('Ne', '≠')):
            code = AXIS.translate_mir(COMPARISON.replace('Le(copy', f'{op}(copy'), 'sample')
            self.assertIn(f'decide (v21 {symbol} v22)', code)
        for op, symbol in (('BitAnd', '&&'), ('BitOr', '||')):
            changed = COMPARISON.replace('Le(copy _21, copy _22)', f'{op}(const true, const false)')
            self.assertIn(f'true {symbol} false', AXIS.translate_mir(changed, 'sample'))
            changed = BRANCH.replace('const 4_u32', f'{op}(copy _2, const 4_u32)')
            self.assertIn(f'v2.toNat {symbol + symbol[0]} 4',
                          translate_sample(changed, ('bool', 'u32'), 'u32'))
        with self.assertRaisesRegex(ValueError, 'wrong operand type'):
            AXIS.translate_mir(COMPARISON.replace('copy _22)', 'const true)'), 'sample')

    def test_cast_widening_and_truncation(self):
        cast = '''
fn sample(_1: u64) -> u32 {
    let mut _0: u32;
    let _2: u128;
    bb0: {
        _2 = copy _1 as u128 (IntToInt);
        _0 = copy _2 as u32 (IntToInt);
        return;
    }
}
'''
        code = translate_sample(cast, ('u64',), 'u32')
        self.assertIn('let v2 := v1.toNat\n', code)
        self.assertIn('let v0 := v2 % (2^32)', code)
        with self.assertRaisesRegex(ValueError, 'out-of-range MIR operand'):
            translate_sample(cast.replace('copy _1 as', 'const 18446744073709551616_u64 as'),
                             ('u64',), 'u32')

    def test_option_values_are_distinct_from_mir_panic_exits(self):
        changed = (BRANCH.replace('_2: u32', '_2: u64').replace('-> u32', '-> Option<u64>')
                   .replace('_0: u32', '_0: Option<u64>')
                   .replace('const 4_u32', 'const Option::<u64>::None')
                   .replace('_0 = copy _2', '_0 = Option::<u64>::Some(copy _2)'))
        code = translate_sample(changed, ('bool', 'u64'), 'Option<u64>')
        dev = changed.replace('const Option', 'Option').replace('_0: Option', '_0: std::option::Option')
        self.assertEqual(translate_sample(dev, ('bool', 'u64'), 'Option<u64>'), code)
        self.assertIn('Option (Option Nat) := do', code)
        self.assertIn('let v0 := (none : Option Nat)\n    return v0', code)
        self.assertIn('let v0 := some (v2.toNat)\n    return v0', code)


class LeanAuditTests(unittest.TestCase):

    def test_audit_ignores_strings_and_nested_comments(self):
        AXIS.audit_lean_source('Example.lean', '''
set_option warningAsError true
/- sorry /- admit -/ unsafe -/
-- native_decide
def x := "axiom hidden"
def y := r#"unsafe "native_decide" sorry"#
def z := s!"sorry {if True then "axiom" else "unsafe"}"
''')

    def test_audit_rejects_proof_escapes(self):
        for source in ('theorem bad : False := by sorry', 'axiom\nbad : False',
                       'unsafe/- note -/def bad := 0', 'by native_decide', 'by admit',
                       's!"{show False from by sorry}"', 'by «sorry»', '«axiom» bad : False',
                       'by «admit»', 'by «native_decide»', '«unsafe» def bad := 0',
                       'attribute [«implemented_by» implementation] spec',
                       '@[extern "foreign"] def bad := 0',
                       'attribute [simp, extern "foreign"] bad', 'partial\ndef bad := bad'):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'forbidden Lean token'):
                AXIS.audit_lean_source('Example.lean', 'set_option warningAsError true\n' + source)

    def test_audit_requires_file_wide_warning_policy(self):
        for source in ('-- set_option warningAsError true',
                       'def opt := "set_option warningAsError true"',
                       'namespace Scoped\nset_option warningAsError true\nend Scoped',
                       'set_option warningAsError true\nin\n#check Nat',
                       'set_option warningAsError true in\n#check Nat',
                       'set_option «warningAsError» true',
                       'set_option warningAsError true\nset_option warningAsError false'):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'file-wide'):
                AXIS.audit_lean_source('Example.lean', source)

    def test_audit_rejects_additional_options(self):
        for directive in ('set_option debug.skipKernelTC true',
                          'set_option «warningAsError» false',
                          'set_option «debug.skipKernelTC» true',
                          'set_option linter.unusedVariables false',
                          'set_option warningAsError true'):
            with self.subTest(directive=directive), self.assertRaises(ValueError):
                AXIS.audit_lean_source('Example.lean', 'set_option warningAsError true\n'
                                       'theorem valid : True := True.intro\n' + directive)
