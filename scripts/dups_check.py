"""Compare the duplicate gate's output with its baseline.

Usage: python3 -I dups_check.py OUT BASELINE [--update]

Both files hold the six count lines (`DUPDEF n`, `DUPTHM n`, `RESTATE n`, `UNUSED n`, `EQUIV n`,
`MISSING n`) and one `TAG: item` line per listed item. The check fails when a count exceeds the
baseline's and prints the items that the baseline does not list. `--update` copies OUT to BASELINE.

Before the comparison, OUT loses the `UNUSED` items that a source file of SymLean names outside
their own declaration. The Lean run reads proof terms, and some uses leave nothing there: a `rfl`
lemma that `simp` applies as a definitional step, a call inside `run_meta` or `#eval`. The
`.ilean` files of the build (the index of the language server, next to the `.olean` files in
`.lake/build/lib/lean/CAS`) list every identifier of a source file with the declaration it stands
in, so a name with a use outside its own declaration is in use. OUT is rewritten without them,
and their names are written to OUT.named. Only the index of a module whose source file exists is
read: a build directory keeps the index of a deleted module.
"""
import json
import os
import shutil
import sys

TAGS = ("DUPDEF", "DUPTHM", "RESTATE", "UNUSED", "EQUIV", "MISSING")
INDEX = ".lake/build/lib/lean/CAS"


def named_in_sources():
    """The constants that a source file of SymLean names outside their own declaration."""
    named = set()
    for root, _, files in os.walk(INDEX):
        for name in files:
            if not name.endswith(".ilean"):
                continue
            with open(os.path.join(root, name), encoding="utf-8") as handle:
                index = json.load(handle)
            if index.get("version") != 5:
                sys.exit(f"dups: {name} has index version {index.get('version')}; this script "
                         "reads version 5 (a usage is four positions and the parent)")
            if not os.path.isfile(index.get("module", "").replace(".", "/") + ".lean"):
                continue
            for key, entry in index.get("references", {}).items():
                if not key.startswith("{"):
                    continue
                constant = json.loads(key).get("c")
                if constant is None:
                    continue
                for usage in entry.get("usages", []):
                    parent = usage[4] if len(usage) > 4 else None
                    if parent != constant["n"]:
                        named.add(constant["n"])
                        break
    return named


def read(path):
    counts, items = {}, set()
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        head = line.split(" ", 1)
        if len(head) == 2 and head[0] in TAGS and head[1].isdigit():
            counts[head[0]] = int(head[1])
        elif line.split(":", 1)[0] in TAGS:
            items.add(line)
    return counts, items


def drop_named(path):
    """Rewrite `path` without the `UNUSED` items that a source file names."""
    named = named_in_sources()
    if not named:
        sys.exit(f"dups: no .ilean files under {INDEX} (run lake build first)")
    lines = open(path, encoding="utf-8").read().split("\n")
    dropped = [line[len("UNUSED: "):] for line in lines
               if line.startswith("UNUSED: ") and line[len("UNUSED: "):] in named]
    kept = [line for line in lines
            if not (line.startswith("UNUSED: ") and line[len("UNUSED: "):] in named)]
    count = sum(line.startswith("UNUSED: ") for line in kept)
    kept = [f"UNUSED {count}" if line.startswith("UNUSED ") and line[7:].isdigit() else line
            for line in kept]
    with open(path, "w", encoding="utf-8") as handle:
        handle.write("\n".join(kept))
    # What this rule removed, for whoever audits it.
    with open(path + ".named", "w", encoding="utf-8") as handle:
        handle.write("".join(f"{name}\n" for name in sorted(dropped)))


out, base = sys.argv[1], sys.argv[2]
drop_named(out)
counts, items = read(out)
if set(counts) != set(TAGS):
    sys.exit(f"dups: {out} lacks some counts (the Lean run failed?)")
if "--update" in sys.argv:
    shutil.copy(out, base)
    print("dups: baseline updated: " + ", ".join(f"{t} {counts[t]}" for t in TAGS))
    sys.exit(0)
bcounts, bitems = read(base)
status = 0
for tag in TAGS:
    mark = "ok  " if counts[tag] <= bcounts.get(tag, 0) else "FAIL"
    if mark == "FAIL":
        status = 1
    print(f"{mark} {tag} {counts[tag]} (baseline {bcounts.get(tag, 0)})")
for line in sorted(items - bitems):
    print(f"new  {line}")
sys.exit(status)
