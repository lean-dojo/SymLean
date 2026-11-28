#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# build.sh SRC OUT JOBS MODULE...: compiles the modules MODULE... (dot names, sources under SRC)
# into OUT with `lean`, outside Lake, JOBS at a time. The modules of one call must not import each
# other; the modules they import are found in OUT and on LEAN_PATH, so run it under `lake env`.
# LEAN_OPTS holds further options of `lean`. With TIMES set to a directory, the report of
# `/usr/bin/time -v` for every module is written to TIMES/MODULE.time. The exit status is zero
# if every module compiled. The script sets two variables of the C library's allocator (below).
set -u
src=$1; out=$2; jobs=$3; shift 3
# A kernel test on large numbers frees gigabytes after every declaration. With these two settings
# the C library keeps its heap instead of returning the top of it to the system. On such tests
# they cut the page faults and the system time to a third, which fits a heap that was returned
# after every declaration and faulted in again; allocations were not traced. Values of the caller
# win.
export MALLOC_TRIM_THRESHOLD_=${MALLOC_TRIM_THRESHOLD_:-68719476736}
export MALLOC_TOP_PAD_=${MALLOC_TOP_PAD_:-268435456}
compile() {
  local m=$1
  local f="$src/${m//.//}.lean" o="$out/${m//.//}"
  mkdir -p "$(dirname "$o")"
  if [[ -n "${TIMES:-}" ]]; then
    LEAN_PATH="$out:$LEAN_PATH" /usr/bin/time -v -o "$TIMES/$m.time" \
      lean -R "$src" ${LEAN_OPTS:-} -o "$o.olean" -i "$o.ilean" "$f"
  else
    LEAN_PATH="$out:$LEAN_PATH" lean -R "$src" ${LEAN_OPTS:-} -o "$o.olean" -i "$o.ilean" "$f"
  fi
}
export -f compile
export src out
printf '%s\n' "$@" | xargs -P "$jobs" -I{} bash -c 'compile {}'
