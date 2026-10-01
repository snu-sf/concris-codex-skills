#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
dest="${CODEX_HOME:-$HOME/.codex}/skills"

skills=(
  concris-proof
  concris-helping-proof
  concris-tame-proof
  clightplus-proof
)

mkdir -p "$dest"

for skill in "${skills[@]}"; do
  src="$repo_root/skills/$skill"
  target="$dest/$skill"

  if [[ ! -d "$src" ]]; then
    echo "Missing skill directory: $src" >&2
    exit 1
  fi

  if [[ -L "$target" ]]; then
    current="$(readlink "$target")"
    if [[ "$current" == "$src" ]]; then
      echo "Already installed: $skill"
      continue
    fi

    echo "Refusing to replace existing symlink: $target -> $current" >&2
    exit 1
  fi

  if [[ -e "$target" ]]; then
    echo "Refusing to replace existing path: $target" >&2
    echo "Move it aside or remove it before installing $skill." >&2
    exit 1
  fi

  ln -s "$src" "$target"
  echo "Installed: $skill"
done

echo "Restart Codex to pick up new or updated skills."
