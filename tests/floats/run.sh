#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of the arithmetic of `cega` as a setting of a whole build. The package `consumer/`
# requires SymLean and proves the bounds of `Bounds.lean`, whose first five theorems call `cega`
# without naming an arithmetic. Lake builds it several times, and no Lean file changes in
# between:
#
# 1. `lake build`: every such call computes with exact rationals.
# 2. `lake -R -Karithmetic=binary64 build`: the lakefile passes the value as the Lean option
#    `weak.cega.arithmetic`, and the same calls compute with binary64 floats. The calls that
#    choose for themselves keep their choice: `cega [use_floats := false]` and
#    `(arith := "exact")` stay exact, `(arith := binary128)` stays binary128.
# 3. `lake -R -Karithmetic=binary128 build`: another format.
# 4. `lake -R -Karithmetic=decimal64 build`: a value that names no arithmetic stops the build
#    with the message of `cega`.
# 5. `lake -R build`: exact rationals again.
# 6. `lake env lean -Dweak.cega.arithmetic=binary64 Bounds.lean`: the flag that Lake passes to
#    Lean, given by hand for one file, with no lakefile line. The trace of FloatLib's check,
#    which proves these bounds first, names binary64 for the calls that follow the build and
#    nothing for the exact ones.
#
# After each build `Show.lean` reads the proofs that the build produced and prints, for each
# theorem, whether the backend of FloatLib that it computes with has exact rational ends or the
# ends of a float format, with the widths of the format, and whether all the theorems have the
# standard axioms; the line is compared. The package `fixed/` sets the option with one line of
# `lakefile.toml` and is built once.
#
# The packages are copied to a scratch directory under `TMPDIR`, next to a link to the
# repository, and their dependencies come from the repository's `.lake/packages` and its build,
# which the test only reads: it stops if Lake would rebuild a module of SymLean. Run it from
# the repository root after `lake build`; it needs python3 and no network. Six builds of one
# module and two runs of `lean` on it, about 20 s each. The exit status is the result.
set -u
repo="$(cd "$(dirname "$0")/../.." && pwd)"
if [[ ! -d "$repo/.lake/packages/mathlib" ]]; then
  echo "$repo/.lake/packages has no dependencies: run lake build first"
  exit 1
fi
scratch="$(mktemp -d "${TMPDIR:-/tmp}/symlean-floats.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
status=0
log="$scratch/lake.log"
: > "$log"
ok() { echo "ok   $1"; }
fail() { echo "FAIL $1"; grep -v '^trace:' "$log" | tail -n 12 | cut -c1-300 | sed 's/^/     /'; status=1; }

ln -s "$repo" "$scratch/symlean"
for package in consumer fixed; do
  mkdir -p "$scratch/$package/.lake"
  cp "$repo/tests/floats/$package/"lakefile.* "$scratch/$package/"
  cp "$repo/tests/floats/Bounds.lean" "$repo/tests/floats/Show.lean" "$scratch/$package/"
  cp "$repo/lean-toolchain" "$scratch/$package/"
  ln -s "$repo/.lake/packages" "$scratch/$package/.lake/packages"
done
# The manifests pin SymLean's dependencies, so that Lake resolves them offline.
python3 - "$repo/lake-manifest.json" "$scratch" <<'EOF'
import json, sys
manifest = json.load(open(sys.argv[1]))
inherited = [dict(entry, inherited=True) for entry in manifest["packages"]
             if entry["name"] != "DSLean"]
symlean = {"type": "path", "scope": "", "name": "SymLean", "manifestFile": "lake-manifest.json",
           "inherited": False, "dir": "../symlean", "configFile": "lakefile.lean"}
for name in ("consumer", "fixed"):
    json.dump({"version": manifest["version"], "packagesDir": ".lake/packages",
               "packages": [symlean] + inherited, "name": name, "lakeDir": ".lake"},
              open(f"{sys.argv[2]}/{name}/lake-manifest.json", "w"), indent=1)
EOF
consumer="$scratch/consumer"
fixed="$scratch/fixed"
# `lake_in dir args` runs `lake args` in `dir`; `shows dir line` checks that `Show.lean` of `dir`,
# elaborated against the build, prints `line`.
lake_in() { (cd "$1" && shift && lake "$@") > "$log" 2>&1; }
shows() { (cd "$1" && lake env lean Show.lean) > "$log" 2>&1 && grep -qxF -- "$2" "$log"; }

# The library must be built: the test reads the repository's build and never writes to it.
if lake_in "$consumer" build --no-build @SymLean/+CAS; then
  ok "the library is built, and Lake reuses it for a package that requires it"
else
  fail "the library is built (run lake build first)"
  exit 1
fi

# What `Show.lean` prints in each arithmetic: the first five theorems follow the build, the next
# four keep their own choice, and the last three do not depend on it (the integral asks for exact
# rationals, the finite statement has no box query, and `cas` computes with exact rationals).
line() {
  echo "bare=$1 closed=$1 configured=$1 query=$1 fast=$1 floatsOff=exact floatsOn=$2" \
    "quad=ieee(15,112) queryExact=exact integral=exact finite=other viaCas=exact" \
    "axioms=standard"
}
exact="$(line exact "ieee(11,52)")"
double="$(line "ieee(11,52)" "ieee(11,52)")"
quad="$(line "ieee(15,112)" "ieee(15,112)")"

if lake_in "$consumer" build Bounds && shows "$consumer" "$exact"; then
  ok "lake build: exact rationals"
else
  fail "lake build: exact rationals"
fi
if lake_in "$consumer" -R -Karithmetic=binary64 build Bounds && shows "$consumer" "$double"; then
  ok "lake -R -Karithmetic=binary64 build: binary64 floats, and the calls that choose keep their choice"
else
  fail "lake -R -Karithmetic=binary64 build: binary64 floats"
fi
if lake_in "$consumer" -R -Karithmetic=binary128 build Bounds && shows "$consumer" "$quad"; then
  ok "lake -R -Karithmetic=binary128 build: binary128 floats"
else
  fail "lake -R -Karithmetic=binary128 build: binary128 floats"
fi
if ! lake_in "$consumer" -R -Karithmetic=decimal64 build Bounds &&
    grep -qF 'the option `cega.arithmetic` does not name an arithmetic' "$log"; then
  ok "lake -R -Karithmetic=decimal64 build: refused with the message of cega"
else
  fail "lake -R -Karithmetic=decimal64 build: refused with the message of cega"
fi
if lake_in "$consumer" -R build Bounds && shows "$consumer" "$exact"; then
  ok "lake -R build: exact rationals again"
else
  fail "lake -R build: exact rationals again"
fi

# The same option on the command line of `lean`, for one file: `-Dweak.cega.arithmetic=…` is what
# Lake passes for the lakefile line. `traced args` elaborates `Bounds.lean` with `args` and the
# trace of FloatLib's check of stated bounds, which names the format of a float check and no
# format for an exact one. `bare` states `≤ 68/25`, and `floatsOff`, which asks for exact
# arithmetic, `≤ 11/4`.
traced() {
  (cd "$consumer" && lake env lean -Dweak.trace.cega.refute=true "$@" Bounds.lean) > "$log" 2>&1
}
if traced -Dweak.cega.arithmetic=binary64 &&
    grep -qF 'FloatLib check in binary64, stated bound ≤ 68/25:' "$log" &&
    ! grep -qF 'FloatLib check, stated bound ≤ 68/25:' "$log" &&
    grep -qF 'FloatLib check, stated bound ≤ 11/4:' "$log" &&
    traced && grep -qF 'FloatLib check, stated bound ≤ 68/25:' "$log" &&
    ! grep -qF ' in binary64, stated bound ≤ 68/25:' "$log"; then
  ok "lean -Dweak.cega.arithmetic=binary64 on one file: binary64 floats, exact without the flag"
else
  fail "lean -Dweak.cega.arithmetic=binary64 on one file: binary64 floats"
fi

# One line of `lakefile.toml` sets the arithmetic of a package.
if lake_in "$fixed" build Bounds && shows "$fixed" "$double"; then
  ok "lakefile.toml with weak.cega.arithmetic = \"binary64\": binary64 floats"
else
  fail "lakefile.toml with weak.cega.arithmetic = \"binary64\": binary64 floats"
fi
exit $status
