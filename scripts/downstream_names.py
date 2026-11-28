"""Write the declarations of SymLean that built downstream projects reference or cite.

Usage, from the repository root after `lake build`:
    python3 -I scripts/downstream_names.py LABEL=DIR [LABEL=DIR ...]

It rewrites `scripts/downstream.names`. Each DIR belongs to a project that requires SymLean. Two
kinds of file are read under it.

* `.ilean` files, which Lean writes next to every `.olean` (give the project's
  `.lake/build/lib/lean`): the index of the language server, which resolves every identifier of
  a source file to a constant and to the module that declares it. Every constant that a module of
  SymLean (`CAS` or `CAS.…`) declares and a module of the project references is listed.
* `.lean` files (give a source directory, such as a blueprint): the names in the strings of
  `(lean := "A, B")`, with which a blueprint cites the theorems it describes. A cited name is
  listed when SymLean declares it, by the `.ilean` files of SymLean's own build in
  `.lake/build/lib/lean`, or when the list held it before: a citation of a declaration that
  SymLean has deleted since stays in the list, so that the gate reports it. The index does not
  list the fields of a structure, so a cited field is not in the list.

The list has one name per line with the labels of the directories that use it. The duplicate
gate (`scripts/Dups.lean`) counts these names as used and reports one that no longer exists, so
a deletion or a rename that would break a downstream project shows up before that project is
rebuilt.

The index holds the identifiers that are written in a source file. It does not see a constant
that only a tactic or a macro puts into a term, such as a `simp` lemma found by its attribute.
LABEL is free text without spaces that names the state read, for instance `PDEAtlas@REV` for the
commit REV of PDEAtlas, or `PDEAtlas@REV+local` for a tree with local commits on top of that one.
Read a tree when no build runs in it: the script stops when a file disappears while it reads or
when a directory gives no name.
"""
import json
import os
import re
import sys

CITATION = re.compile(r'\(lean\s*:=\s*"([^"]*)"\)')


def indexes(directory):
    """The parsed `.ilean` files under `directory`."""
    for root, _, files in os.walk(directory):
        for name in files:
            if name.endswith(".ilean"):
                with open(os.path.join(root, name), encoding="utf-8") as handle:
                    yield json.load(handle)


def declared(build_dir):
    """The constants that the modules of SymLean under `build_dir` declare."""
    found = set()
    for index in indexes(build_dir):
        if index.get("module", "").split(".")[0] == "CAS":
            found.update(index.get("decls", {}))
    return found


def references(directory):
    """The constants declared in SymLean that the `.ilean` files under `directory` reference."""
    found = set()
    for index in indexes(directory):
        if index.get("module", "").split(".")[0] == "CAS":
            continue
        for key in index.get("references", {}):
            if not key.startswith("{"):
                continue
            constant = json.loads(key).get("c")
            if constant and constant.get("m", "").split(".")[0] == "CAS":
                found.add(constant["n"])
    return found


def citations(directory):
    """The names in the `(lean := "…")` strings of the `.lean` files under `directory`."""
    found = set()
    for root, folders, files in os.walk(directory):
        folders[:] = [folder for folder in folders if folder not in (".lake", ".git")]
        for name in files:
            if not name.endswith(".lean"):
                continue
            with open(os.path.join(root, name), encoding="utf-8") as handle:
                text = handle.read()
            for match in CITATION.finditer(text):
                found.update(part.strip() for part in match.group(1).split(","))
    return found


OUTPUT = "scripts/downstream.names"


def listed_before():
    """The names of the present list, without their labels."""
    if not os.path.isfile(OUTPUT):
        return set()
    with open(OUTPUT, encoding="utf-8") as handle:
        return {line.split()[0] for line in handle if line.strip() and not line.startswith("#")}


def main():
    ours = declared(".lake/build/lib/lean")
    if not ours:
        sys.exit("downstream_names: no .ilean files of SymLean in .lake/build/lib/lean; "
                 "run it from the repository root after lake build")
    before = listed_before()
    users = {}
    labels = []
    for argument in sys.argv[1:]:
        label, _, directory = argument.partition("=")
        if not directory or not os.path.isdir(directory):
            sys.exit(f"downstream_names: {argument}: expected LABEL=DIR")
        labels.append(label)
        try:
            names = references(directory) | (citations(directory) & (ours | before))
        except FileNotFoundError as error:
            sys.exit(f"downstream_names: {error.filename} disappeared while reading {directory}; "
                     "is a build running there?")
        if not names:
            sys.exit(f"downstream_names: {directory} gives no name of SymLean")
        for name in names:
            users.setdefault(name, []).append(label)
    if not labels:
        sys.exit("downstream_names: expected LABEL=DIR [LABEL=DIR ...]")
    lines = [
        "# Declarations of SymLean that downstream projects reference in their built modules or",
        "# cite in a blueprint (scripts/downstream_names.py). The duplicate gate counts them as",
        "# used and reports one that no longer exists.",
        "# Read from: " + ", ".join(labels) + ".",
    ]
    lines += [f"{name} {' '.join(users[name])}" for name in sorted(users)]
    with open(OUTPUT, "w", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")
    print(f"downstream_names: {len(users)} names in {OUTPUT}")


if __name__ == "__main__":
    main()
