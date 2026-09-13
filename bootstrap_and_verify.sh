#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if [[ -d "$HOME/.elan/bin" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
if ! command -v lake >/dev/null 2>&1; then
  echo 'Install Lean/Elan first: https://lean-lang.org/install/' >&2
  exit 127
fi
lake update
lake exe cache get
exec bash verify.sh
