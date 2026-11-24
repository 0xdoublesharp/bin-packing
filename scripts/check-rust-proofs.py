#!/usr/bin/env python3
"""Check Lean refinement theorems against the compiler MIR of production predicates."""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import NamedTuple

ROOT = Path(__file__).resolve().parent.parent
PROOFS = ROOT / 'proofs'
LEAN_FLAGS = ('-DwarningAsError=true', '-Ddebug.skipKernelTC=false')
LOCAL = r'_\d+'
UINT = r'u(?:32|64|128)'
OPTION = r'(?:std::option::)?Option<u64>'
TYPE = rf'(?:bool|{UINT}|{OPTION})'
OPERAND = rf'(?:(?:copy|move) {LOCAL}|const (?:\d+_{UINT}|true|false))'
DECLARATION = re.compile(rf'let (?:mut )?({LOCAL}): ({TYPE}|\({UINT}, bool\));')
DEBUG = re.compile(r'debug [a-z_][a-z_0-9]* => [^;]+;')
STORAGE = re.compile(rf'Storage(Live|Dead)\(({LOCAL})\);')
BLOCK = re.compile(r'bb(\d+): \{')
ASSIGNMENT = re.compile(rf'({LOCAL}) = (.+);')
CAST = re.compile(rf'({OPERAND}) as ({UINT}) \(IntToInt\)')
BINARY = re.compile(
    rf'(AddWithOverflow|SubWithOverflow|MulWithOverflow|Add|Sub|Mul|Div|'
    rf'Le|Lt|Ge|Gt|Eq|Ne|BitAnd|BitOr)\(({OPERAND}), ({OPERAND})\)'
)
FIELD = re.compile(rf'(?:copy|move) \(({LOCAL})\.(0|1): ({UINT}|bool)\)')
SATURATING = rf'(?:core::num::<impl ({UINT})>::saturating_add|'
SATURATING += rf'(?:core|std)::intrinsics::saturating_add::<({UINT})>)'
MINIMUM = rf'(?:core|std)::cmp::min::<({UINT})>'
ORD_MINIMUM = rf'<({UINT}) as Ord>::min'
SCALAR_CALL = re.compile(
    rf'({LOCAL}) = (?:{SATURATING}|{MINIMUM}|{ORD_MINIMUM})\(({OPERAND}), ({OPERAND})\)'
    r' -> \[return: bb(\d+), unwind (?:continue|unreachable)\];'
)
GUARD = re.compile(
    rf'assert\((!?)(.+?), "(?:[^"\\]|\\.)*"((?:, {OPERAND})*)\)'
    r' -> \[success: bb(\d+), unwind (?:continue|unreachable)\];'
)
SWITCH = re.compile(rf'switchInt\(({OPERAND})\) -> \[([01]): bb(\d+), otherwise: bb(\d+)\];')
GOTO = re.compile(r'goto -> bb(\d+);')
OPTION_SOME = re.compile(rf'(?:std::option::)?Option::<u64>::Some\(({OPERAND})\)')
OPTION_NONE = re.compile(r'(?:const )?(?:std::option::)?Option::<u64>::None')
COMPARISONS = dict(Le='≤', Lt='<', Ge='≥', Gt='>', Eq='=', Ne='≠')
RAW_STRING_START = re.compile(r'r(\#*)"')
CHARACTER_LITERAL = re.compile(r"'(?:[^'\\\n]|\\.)'")


class Value(NamedTuple):
    rust_type: str
    lean: str
    overflow_args: tuple | None = None
    zero_operand: str | None = None


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_blocks(lines, index):
    """Parse the complete block inventory before following any control-flow edge."""
    blocks = {}
    while index < len(lines):
        header = BLOCK.fullmatch(lines[index])
        require(header is not None, f'expected MIR block header: {lines[index]}')
        block = int(header[1])
        require(block not in blocks, f'duplicate MIR block: bb{block}')
        index += 1
        start = index
        while index < len(lines) and lines[index] != '}':
            index += 1
        require(start < index < len(lines), f'missing instructions or closing brace in bb{block}')
        blocks[block] = lines[start:index]
        index += 1
    return blocks


def translate_mir(mir, name, source='end_with_gap_at_most', parameters=('u32',) * 4,
                  result='bool'):
    """Translate an acyclic, typed MIR subset. Outer Option.none represents a panic."""
    require(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) is not None,
            f'invalid generated Lean name: {name}')
    require(all(kind in ('bool', 'u32', 'u64', 'u128') for kind in parameters),
            'unsupported MIR parameter type')
    require(result in ('bool', 'u32', 'u64', 'u128', 'Option<u64>'),
            'unsupported MIR result type')
    signature = {f'_{index}': kind for index, kind in enumerate(parameters, 1)}
    arguments = ', '.join(f'{var}: {kind}' for var, kind in signature.items())
    result_pattern = OPTION if result == 'Option<u64>' else result
    pattern = re.compile(
        rf'^fn (?:[a-z_][a-z_0-9]*::)*{re.escape(source)}\({re.escape(arguments)}\)'
        rf' -> {result_pattern} \{{\n(.*?)^\}}', re.MULTILINE | re.DOTALL)
    bodies = pattern.findall(mir)
    require(len(bodies) == 1, f'expected one production predicate {source} in the crate MIR')
    lines = [line.strip() for line in bodies[0].splitlines() if line.strip()]
    declarations = dict(signature)
    index = depth = 0
    while index < len(lines) and not BLOCK.fullmatch(lines[index]):
        line = lines[index]
        if re.fullmatch(r'scope \d+ \(inlined .+\) \{', line):
            depth += 1
        elif line == '}' and depth:
            depth -= 1
        elif not DEBUG.fullmatch(line):
            local = DECLARATION.fullmatch(line)
            require(local is not None, f'unsupported MIR declaration: {line}')
            var, rust_type = local.groups()
            require(var not in declarations, f'duplicate MIR local: {var}')
            declarations[var] = rust_type.removeprefix('std::option::')
        index += 1
    require(depth == 0, 'unclosed MIR debug scope')
    require(declarations.get('_0') == result, 'wrong MIR return local type')

    blocks = read_blocks(lines, index)
    explicit_storage = {match[2] for line in lines[index:] if (match := STORAGE.fullmatch(line))}
    require(not explicit_storage.intersection(signature.keys() | {'_0'}),
            'explicit storage for MIR input or return local')
    visited = set()
    # Model unsigned inputs as bitvectors and unsigned intermediates as their natural values.
    lean_parameters = ' '.join(
        f'(v{var[1:]} : {"Bool" if kind == "bool" else "BitVec " + kind[1:]})'
        for var, kind in signature.items()
    )
    lean_result = {'bool': 'Bool', 'Option<u64>': '(Option Nat)'}.get(result, 'Nat')
    output = [f'def {name} {lean_parameters} : Option {lean_result} := do']
    inputs = {var: Value(kind, f'v{var[1:]}' + ('' if kind == 'bool' else '.toNat'))
              for var, kind in signature.items()}

    def emit_block(block, live, values, nonzero, path, indent):
        require(block in blocks, f'unsupported MIR instruction: target bb{block} does not exist')
        require(block not in path, f'cyclic MIR control flow at bb{block}')
        visited.add(block)
        path = path | {block}
        statements = blocks[block]

        def emit(line):
            output.append(' ' * indent + line)

        def read(var, expected=None):
            value = values.get(var)
            require(
                var in live and value is not None and (expected is None or value.rust_type == expected),
                f'expected initialized {expected or declarations.get(var, "known")} MIR local: {var}',
            )
            return value

        def operand(token, expected=None):
            # Every supported type is Copy and cannot have a destructor.
            if local := re.fullmatch(rf'(?:copy|move) ({LOCAL})', token):
                return read(local[1], expected)
            literal = re.fullmatch(rf'const (?:(\d+)_({UINT})|(true|false))', token)
            require(literal is not None, f'unsupported MIR operand: {token}')
            digits, kind, boolean = literal.groups()
            if boolean:
                value = Value('bool', boolean)
            else:
                require(int(digits) < 2**int(kind[1:]), f'out-of-range MIR operand: {token}')
                value = Value(kind, str(int(digits)))
            require(expected is None or value.rust_type == expected, f'wrong operand type: {token}')
            return value

        def pair_field(field):
            var, component, kind = field.groups()
            pair_kind = declarations.get(var, '')
            require(re.fullmatch(rf'\({UINT}, bool\)', pair_kind) is not None,
                    f'expected overflow pair: {var}')
            pair = read(var, pair_kind)
            expected = pair_kind[1:].split(',')[0] if component == '0' else 'bool'
            require(kind == expected, f'wrong type for MIR projection from {var}')
            return Value(kind, f'{pair.lean}.{int(component) + 1}',
                         pair.overflow_args if component == '1' else None)

        def store(var, value):
            require(var in live and var not in values,
                    f'MIR assignment requires live, uninitialized storage: {var}')
            require(declarations.get(var) == value.rust_type, f'wrong result type for MIR local: {var}')
            bound = f'v{var[1:]}'
            emit(f'let {bound} := {value.lean}')
            values[var] = value._replace(lean=bound)

        def binary(op, left, right):
            lhs = operand(left)
            kind, a = lhs.rust_type, lhs.lean
            b = operand(right, kind).lean
            numeric = re.fullmatch(UINT, kind) is not None
            if op in COMPARISONS:
                require(numeric or (kind == 'bool' and op in ('Eq', 'Ne')),
                        f'unsupported typed MIR operation: {op} on {kind}')
                zero_operand = None
                if numeric and op == 'Eq' and '0' in (a, b):
                    zero_operand = b if a == '0' else a
                return Value('bool', f'decide ({a} {COMPARISONS[op]} {b})', zero_operand=zero_operand)
            if op in ('BitAnd', 'BitOr'):
                require(numeric or kind == 'bool', f'unsupported typed MIR operation: {op} on {kind}')
                symbol = '&' if op == 'BitAnd' else '|'
                return Value(kind, f'{a} {symbol * (3 if numeric else 2)} {b}')
            require(numeric, f'unsupported typed MIR operation: {op} on {kind}')
            if op == 'Div':
                require(b in nonzero, 'MIR division lacks a dominating nonzero guard')
                return Value(kind, f'{a} / {b}')

            modulus = f'2^{kind[1:]}'
            base = op.removesuffix('WithOverflow')
            if base == 'Sub':
                wrapped = f'(if {a} < {b} then {a} + {modulus} - {b} else {a} - {b})'
                overflow = f'{a} < {b}'
            else:
                exact = f'{a} {"+" if base == "Add" else "*"} {b}'
                wrapped = f'({exact}) % ({modulus})'
                overflow = f'{modulus} ≤ {exact}'
            if op.endswith('WithOverflow'):
                return Value(f'({kind}, bool)', f'({wrapped}, decide ({overflow}))', (a, b))
            return Value(kind, wrapped)

        for line in statements[:-1]:
            if storage := STORAGE.fullmatch(line):
                event, var = storage.groups()
                require(var in declarations, f'unknown MIR storage local: {var}')
                if event == 'Live':
                    require(var not in live and var not in values, f'MIR storage reused: {var}')
                    live.add(var)
                else:
                    require(var in live, f'MIR storage ended while inactive: {var}')
                    live.remove(var)
                continue
            assignment = ASSIGNMENT.fullmatch(line)
            require(assignment is not None, f'unsupported MIR instruction: {line}')
            var, rhs = assignment.groups()
            if match := CAST.fullmatch(rhs):
                value = operand(match[1])
                kind = match[2]
                require(re.fullmatch(UINT, value.rust_type) is not None, f'unsupported MIR cast: {rhs}')
                expr = value.lean
                if int(value.rust_type[1:]) > int(kind[1:]):
                    expr += f' % (2^{kind[1:]})'
                store(var, Value(kind, expr))
            elif match := BINARY.fullmatch(rhs):
                store(var, binary(*match.groups()))
            elif match := FIELD.fullmatch(rhs):
                store(var, pair_field(match))
            elif match := OPTION_SOME.fullmatch(rhs):
                store(var, Value('Option<u64>', f'some ({operand(match[1], "u64").lean})'))
            elif OPTION_NONE.fullmatch(rhs):
                store(var, Value('Option<u64>', '(none : Option Nat)'))
            elif re.fullmatch(OPERAND, rhs):
                store(var, operand(rhs))
            else:
                raise ValueError(f'unsupported MIR expression: {rhs}')

        line = statements[-1]

        def follow(target, *, branch=False):
            emit_block(int(target), live.copy() if branch else live,
                       values.copy() if branch else values, nonzero.copy() if branch else nonzero,
                       path, indent + 2 if branch else indent)

        if line == 'return;':
            emit(f'return {read("_0", result).lean}')
        elif match := GOTO.fullmatch(line):
            follow(match[1])
        elif match := SWITCH.fullmatch(line):
            condition, label, explicit, other = match.groups()
            true, false = (other, explicit) if label == '0' else (explicit, other)
            emit(f'if {operand(condition, "bool").lean} then do')
            follow(true, branch=True)
            emit('else do')
            follow(false, branch=True)
        elif match := GUARD.fullmatch(line):
            negate, token, diagnostics, target = match.groups()
            condition = pair_field(field) if (field := FIELD.fullmatch(token)) else operand(token)
            require(condition.rust_type == 'bool', 'MIR guard must assert a bool')
            diagnostic_args = tuple(operand(arg).lean for arg in diagnostics.split(', ')[1:])
            if condition.overflow_args is not None:
                require(negate and condition.overflow_args == diagnostic_args,
                        'overflow exit must check the corresponding operation')
            if negate and condition.zero_operand is not None:
                nonzero.add(condition.zero_operand)
            rejects = condition.lean if negate else f'!({condition.lean})'
            emit(f'let _ ← if {rejects} then none else some ()')
            follow(target)
        elif match := SCALAR_CALL.fullmatch(line):
            var, primitive, intrinsic, minimum, ord_minimum, left, right, target = match.groups()
            saturating = primitive or intrinsic
            kind = saturating or minimum or ord_minimum
            a, b = operand(left, kind).lean, operand(right, kind).lean
            expr = f'min (2^{kind[1:]} - 1) ({a} + {b})' if saturating else f'min {a} {b}'
            store(var, Value(kind, expr))
            follow(target)
        else:
            raise ValueError(f'unsupported MIR instruction: {line}')

    emit_block(0, set(declarations) - explicit_storage, inputs, set(), set(), 2)
    require(visited == blocks.keys(), 'unexpected MIR block outside entry control flow')
    return '\n'.join(output)


def lean_code(source):
    """Mask comments and literal text, retaining line breaks and interpolated terms."""
    masked = list(source)

    def mask(start, end):
        masked[start:end] = ['\n' if c == '\n' else ' ' for c in source[start:end]]

    def string(start, interpolated=False):
        index = start + 1
        while index < len(source):
            if source[index] == '\\':
                index += 2
                continue
            if source[index] == '"':
                mask(start, index + 1)
                return index + 1
            if interpolated and source[index] == '{':
                mask(start, index + 1)
                index = code(index + 1, in_interpolation=True)
                start = index
            index += 1
        raise ValueError('unterminated Lean string')

    def code(index, in_interpolation=False):
        braces = 0
        while index < len(source):
            if source.startswith('--', index):
                end = source.find('\n', index)
                end = len(source) if end == -1 else end
                mask(index, end)
                index = end
            elif source.startswith('/-', index):
                start, depth = index, 1
                index += 2
                while depth and index < len(source):
                    if source.startswith('/-', index):
                        depth += 1
                        index += 2
                    elif source.startswith('-/', index):
                        depth -= 1
                        index += 2
                    else:
                        index += 1
                require(depth == 0, 'unterminated Lean block comment')
                mask(start, index)
            elif source[index] == '«':
                end = source.find('»', index + 1)
                require(end != -1, 'unterminated Lean escaped identifier')
                index = end + 1
            elif source[index] == '"':
                index = string(index, index > 0 and source[index - 1] == '!')
            elif (raw := RAW_STRING_START.match(source, index)) and (
                    index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'")):
                closing = '"' + raw[1]
                end = source.find(closing, raw.end())
                require(end != -1, 'unterminated Lean raw string')
                end += len(closing)
                mask(index, end)
                index = end
            elif char := CHARACTER_LITERAL.match(source, index):
                mask(index, char.end())
                index = char.end()
            else:
                if in_interpolation and source[index] == '}':
                    if braces == 0:
                        return index
                    braces -= 1
                elif in_interpolation and source[index] == '{':
                    braces += 1
                index += 1
        require(not in_interpolation, 'unterminated Lean string interpolation')
        return index

    code(0)
    return ''.join(masked)


def audit_lean_source(path, source):
    try:
        code = lean_code(source)
    except ValueError as error:
        raise ValueError(f'{path}: {error}') from error
    # Keep offsets intact and treat escaped identifier delimiters as token boundaries.
    normalized = code.replace('«', ' ').replace('»', ' ')
    forbidden = re.search(
        r"(?<![\w'])(?:sorry|admit|axiom|native_decide|unsafe|debug\s*\.\s*skipKernelTC|"
        r"implemented_by|extern|partial\s+def)(?![\w'])", normalized)
    if forbidden:
        line = code.count('\n', 0, forbidden.start()) + 1
        raise ValueError(f'{path}:{line}: forbidden Lean token {source[forbidden.start():forbidden.end()]}')
    policy = 'set_option warningAsError true'
    header = re.match(r'\s*(?:(?:prelude|(?:public |meta )?import \S+)\s+)*'
                      rf'({policy})[ \t]*(?:\n|\Z)', code)
    require(header is not None and source[header.start(1):header.end(1)] == policy
            and re.match(r"\s*in(?![\w'])", normalized[header.end():]) is None
            and len(re.findall(r"(?<![\w'])set_option(?![\w'])", normalized)) == 1,
            f'{path}: expected exactly one file-wide {policy} and no other set_option')


def audit_lean_environment(pin):
    config = tomllib.loads((PROOFS / 'lakefile.toml').read_text())
    modules = list(dict.fromkeys(root for lib in config['lean_lib'] for root in lib['roots']))
    require(modules, 'no Lake proof roots to audit')
    if 'Check' not in modules:
        modules.append('Check')
    require(all(re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', module, re.ASCII)
                for module in modules), 'invalid Lake proof module name')
    imports = '\n'.join(f'import {module}' for module in modules)
    module_names = ', '.join(f'`{module}' for module in modules)
    audit = f'''import Lean
{imports}

open Lean in
run_cmd do
  let modules := [{module_names}]
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  let env ← getEnv
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx]!
    unless modules.contains owner do continue
    if info.isAxiom then
      throwError "unexpected axiom declaration {{name}} in {{owner}}"
    if info.isTheorem then
      for assumption in ← Lean.collectAxioms name do
        unless allowed.contains assumption do
          throwError "unexpected axiom {{assumption}} in theorem {{name}} from {{owner}}"
      theorems := theorems + 1
  if theorems == 0 then
    throwError "no local Lean theorems found"
  IO.println s!"Kernel-audited {{theorems}} local Lean theorems."
'''
    # Build all modules from source with the audit flags, including the checker's entry module.
    with TemporaryDirectory(prefix='bin-packing-lean-audit-') as directory:
        work = Path(directory)
        lakefile = work / 'lakefile.toml'
        lakefile.write_text(f'''name = "PackingProofAudit"
buildDir = {json.dumps(str(work / 'build'), ensure_ascii=False)}
moreLeanArgs = {json.dumps(LEAN_FLAGS)}

[[lean_lib]]
name = "ProofAudit"
roots = {json.dumps(modules)}
''')
        lake = ['elan', 'run', pin, 'lake', '--no-cache', '--file', str(lakefile)]
        subprocess.run([*lake, 'build', 'ProofAudit'], cwd=PROOFS, check=True)
        subprocess.run([*lake, 'env', 'lean', *LEAN_FLAGS, '--stdin'],
                       cwd=PROOFS, input=audit, text=True, check=True)


def audit_tcb():
    sources = sorted(path for path in PROOFS.rglob('*.lean')
                     if '.lake' not in path.relative_to(PROOFS).parts)
    require(sources, 'no Lean proof sources to audit')
    for path in sources:
        audit_lean_source(path.relative_to(ROOT), path.read_text())

    rust_pin = ROOT / 'rust-toolchain.toml'
    lean_pin = PROOFS / 'lean-toolchain'
    rust = tomllib.loads(rust_pin.read_text())['toolchain']['channel']
    lean = lean_pin.read_text().strip()
    require(re.fullmatch(r'\d+\.\d+\.\d+', rust), f'Rust toolchain is not an exact release: {rust}')
    require(re.fullmatch(r'leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?', lean),
            f'Lean toolchain is not an exact release: {lean}')
    rust_version = subprocess.check_output(['rustc', '--version'], cwd=ROOT, text=True).strip()
    lean_version = subprocess.check_output(['elan', 'run', lean, 'lean', *LEAN_FLAGS, '--version'],
                                           cwd=PROOFS, text=True).strip()
    require(rust_version.startswith(f'rustc {rust} '), f'Rust pin mismatch: {rust_version}')
    require(lean_version.startswith(f'Lean (version {lean.split(":v")[1]},'),
            f'Lean pin mismatch: {lean_version}')
    print(f'Audited {len(sources)} Lean source files for proof escapes and warnings policy.', flush=True)
    audit_lean_environment(lean)
    print(f'rust-toolchain.toml pins {rust}: {rust_version}')
    print(f'proofs/lean-toolchain pins {lean}: {lean_version}')
    for file in ('Cargo.lock', 'bindings/node/pnpm-lock.yaml', 'bindings/wasm/pnpm-lock.yaml'):
        content = (ROOT / file).read_bytes()
        require(content.strip(), f'empty lockfile: {file}')
        print(f'SHA-256 {hashlib.sha256(content).hexdigest()}  {file}')
    print('Refinement TCB: pinned rustc MIR, the MIR translator, and the pinned Lean kernel and imports.')


def build_generated(work, lean, env, module_name, definitions):
    module = work / f'{module_name}.lean'
    module.write_text(f'import Lean\n\nset_option warningAsError true\n\nnamespace {module_name}\n\n'
                      + '\n\n'.join(definitions) + f'\n\nend {module_name}\n')
    subprocess.run([*lean, '-o', f'{module_name}.olean', module.name], cwd=work, env=env, check=True)


def check(bindings):
    pin = (PROOFS / 'lean-toolchain').read_text().strip()
    lean = ['elan', 'run', pin, 'lean', *LEAN_FLAGS]
    with TemporaryDirectory(prefix='bin-packing-rust-proofs-') as directory:
        work = Path(directory)
        env = {**os.environ, 'LEAN_PATH': str(work)}
        if bindings:
            modules = {'GeneratedJsIntegers': []}
            processes = []
            for target, args in (('node', ['-p', 'bin-packing-node']),
                                 ('wasm', ['-p', 'bin-packing-wasm', '--target', 'wasm32-unknown-unknown'])):
                for profile in ('dev', 'release'):
                    specs = [('GeneratedJsIntegers', f'{target}_{profile}_sum', 'is_safe_js_sum',
                              ('u64', 'u64'), 'bool')]
                    if profile == 'release':
                        specs.append(('GeneratedJsIntegers', target, 'is_safe_js_integer',
                                      ('u64',), 'bool'))
                    processes.append(([*args, '--profile', profile], specs))
            proofs = ['RustJsIntegers.lean']
        else:
            modules = {'GeneratedRustAxis': [], 'GeneratedRustProduction': []}
            cargo = ['-p', 'bin-packing', '--no-default-features', '--features', 'one-d,two-d,three-d']
            processes = []
            for profile, suffix in (('dev', 'checked'), ('release', 'optimized')):
                specs = [('GeneratedRustAxis', suffix, 'end_with_gap_at_most', ('u32',) * 4, 'bool')]
                for source, parameters, result in (
                    ('effective_axis_bound', ('u32', 'u32', 'bool'), 'u32'),
                    ('fits_trimmed_axis', ('u32',) * 5, 'bool'),
                    ('area_u64', ('u32', 'u32'), 'u64'),
                    ('scale_threshold', ('u32',) * 3, 'u32'),
                    ('scale_floor', ('u32', 'u32'), 'u32'),
                ):
                    specs.append(('GeneratedRustProduction', f'{source}_{suffix}', source,
                                  parameters, result))
                processes.append(([*cargo, '--profile', profile], specs))
            proofs = ['RustAxis.lean', 'RustProduction.lean']

        for index, (cargo_args, specs) in enumerate(processes):
            mir_path = work / f'{index}.mir'
            jobs = ['-j', os.environ['COMPUTE_JOBS']] if 'COMPUTE_JOBS' in os.environ else []
            subprocess.run(['cargo', 'rustc', '--locked', '--lib', *jobs, *cargo_args,
                            '--', f'--emit=mir={mir_path}'], cwd=ROOT, check=True)
            mir = mir_path.read_text()
            for module, name, source, parameters, result in specs:
                modules[module].append(translate_mir(mir, name, source, parameters, result))
            mir_path.unlink()
        if not bindings:
            subprocess.run([*lean, '-o', str(work / 'Packing.olean'), 'Packing.lean'],
                           cwd=PROOFS, env=env, check=True)
        for module, definitions in modules.items():
            build_generated(work, lean, env, module, definitions)
        for proof in proofs:
            subprocess.run([*lean, proof], cwd=PROOFS, env=env, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--bindings', action='store_true', help='check Node and wasm32 predicates')
    mode.add_argument('--audit-tcb', action='store_true', help='audit proof sources and toolchain provenance')
    args = parser.parse_args()
    if (ROOT / '.scratch.json').is_file() and os.environ.get('BIN_PACKING_SCRATCH_ACTIVE') != '1':
        return subprocess.run(
            [sys.executable, '-B', 'scripts/scratch.py', 'run', sys.executable, '-B',
             'scripts/check-rust-proofs.py', *sys.argv[1:]], cwd=ROOT, check=False).returncode
    if args.audit_tcb:
        audit_tcb()
        return 0
    check(args.bindings)
    if args.bindings:
        print('Lean checked Node and wasm32 safe integers and both payload-addition MIR profiles.')
    else:
        print('Lean checked six production Rust arithmetic predicates in dev and release MIR.')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except ValueError as error:
        sys.exit(str(error))
