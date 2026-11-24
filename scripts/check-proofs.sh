#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "${script_dir}/.."

if [[ -f .scratch.json && ${BIN_PACKING_SCRATCH_ACTIVE:-} != 1 ]]; then
  exec python3 scripts/scratch.py run ./scripts/check-proofs.sh "$@"
fi

export PATH="${PATH}:${HOME}/.elan/bin"
if ! command -v elan >/dev/null 2>&1; then
  printf 'error: elan is required to run the pinned Lean proofs\n' >&2
  exit 127
fi

if [[ $# == 0 ]]; then
  cargo test -p bin-packing --locked --no-default-features \
    --features one-d,two-d,three-d,irregular --test lean_certificates -- --ignored --nocapture
  python3 -B scripts/check-rust-proofs.py
  exec python3 -B scripts/check-rust-proofs.py --audit-tcb
fi

if [[ $# != 1 || ($1 != --verify && $1 != --bindings) ]]; then
  printf 'usage: %s [--verify|--bindings]\n' "$0" >&2
  exit 2
fi

cd proofs
toolchain="$(<lean-toolchain)"
elan run "$toolchain" lake build Packing >&2
if [[ $1 == --verify ]]; then
  exec elan run "$toolchain" lake env lean --run Check.lean --verify
fi

node ../bindings/test/lean-certificates.cjs |
  elan run "$toolchain" lake env lean --run Check.lean
exec python3 -B ../scripts/check-rust-proofs.py --bindings
