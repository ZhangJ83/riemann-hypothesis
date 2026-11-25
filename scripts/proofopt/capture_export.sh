#!/usr/bin/env bash
# Run in the proof checkout; the tool itself can live in another worktree.
# This is a capture pipeline, not a fresh-build or independent-kernel check.
set -euo pipefail
if [[ $# != 1 ]]; then echo "usage: bash capture_export.sh OUT_DIR" >&2; exit 2; fi
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$(git rev-parse --show-toplevel)"
out="$(realpath -m "$1")"
mkdir -p "$out"
for f in solution.ndjson ownership.ndjson capture.json; do
  if [[ -e "$out/$f" ]]; then echo "refusing to overwrite $out/$f" >&2; exit 2; fi
done
if [[ -n "$(git status --porcelain --untracked-files=normal -- src lean-toolchain lakefile.toml lake-manifest.json comparator.json export-targets.txt comparator)" ]]; then
  echo "proof checkout must be clean" >&2; exit 2
fi
command -v lake >/dev/null
lake build --no-build Main
git ls-files 'src/*.lean' | python3 -c 'import sys; print("\n".join(x.strip()[4:-5].replace("/", ".") for x in sys.stdin if x.strip()))' > "$out/modules.txt"
# Include the exact upstream export roots and built-in support declarations.
mapfile -t targets < <(tr '[:space:]' '\n' < export-targets.txt | sed '/^$/d')
lake env leanexport Main -- "${targets[@]}" > "$out/solution.ndjson"
lake env lean --run "$here/OwnerManifest.lean" "$out/modules.txt" "$out/ownership.ndjson"
git rev-parse HEAD > "$out/commit.txt"
lake env lean --version > "$out/lean-version.txt"
python3 - "$out" <<'PY'
import hashlib, json, pathlib, sys
p=pathlib.Path(sys.argv[1])
def digest(name):
    with (p/name).open("rb") as f:
        return hashlib.file_digest(f,"sha256").hexdigest()
manifest=json.loads(pathlib.Path("lake-manifest.json").read_text())
meta={"schema":1,"commit":(p/"commit.txt").read_text().strip(),
      "lean":(p/"lean-version.txt").read_text().strip(),
      "mathlib":next(x["rev"] for x in manifest["packages"] if x["name"]=="mathlib"),
      "export_sha256":digest("solution.ndjson"),"ownership_sha256":digest("ownership.ndjson"),
      "modules_sha256":digest("modules.txt"),"capture_mode":"existing-compiled-artifacts",
      "independent_kernel_verified":False,"clean_build_cpu_seconds":None}
(p/"capture.json").write_text(json.dumps(meta,indent=2)+"\n")
PY
