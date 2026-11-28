/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Sha256
public import Mathlib.Util.CompileInductive

/-!
# Tables as text: one entry per line

## Motivation

The tables of a certificate are written as text files, and two readers take them in: the build,
which embeds a file in a module, and a program that runs over the files. If each reader had its
own way to read the text, one file could stand for two different tables, and a statement proved
by one route would not be about the numbers that the other route tested. What is the one format,
and the one function that reads an entry of it?

## The idea

A table of entries of `w` bits is a text with one entry per line: exactly `w / 4` hexadecimal
digits, the most significant first, and a line feed. Every line has the same length, so line `i`
starts at byte `i * (w / 4 + 1)` and an entry is found without reading the lines before it. The
digits are a `w`-bit two's complement number.

`hexEntry? w text i` reads line `i`. It returns the number with its sign bit flipped, which is
the biased form of a slot, and it returns `none` when the line is not in the format: a byte that
is not a digit, a byte other than a line feed after the digits, a text that ends before the line
does, or a width that is not a positive multiple of 4. Nothing is skipped and nothing is
guessed. A reader that needs a number for every index gives an absent entry an invalid ball,
which no comparison accepts.

## Main results

* `hexEntry?` (a construction, for all widths, texts and indices): the entry of line `i`, or
  `none`. No theorem is stated about it here: the two readers below call this one function,
  which is what makes their tables agree.

## Relations

`pinned_hex%` ([Shard](Shard.lean)) reads every entry of an embedded text with `hexEntry?` and
refuses a text with a line that is not in the format. `Run.look?` ([Run](Run.lean)) reads the
files of a run with the same function, and `entryBall?` ([Table](Table.lean)) turns `none` into
an invalid ball. So an embedded table and a table of a run hold the same numbers whenever their
bytes are the same. A malformed line makes `pinned_hex%` refuse its text, and in a run it is an
absent entry, with whose invalid ball every comparison fails. The biased form is that of
`signedSlot` ([PackedSlots](../Numerics/PackedSlots.lean)), which `entryVal`
([Table](Table.lean)) turns into a real number. `Sha256.hexDigit?` ([Sha256](Sha256.lean))
reads one digit.

## Scope

There is one format. A table in decimal or in floating-point form needs its own reader. No
theorem relates the format to a program that writes it: `scripts/cert_synthetic.py` writes it,
and what it wrote is checked only through what Lean reads. Upper-case digits are accepted, so
two texts can hold the same entries; the digest of a file pins its bytes, not its entries.
-/

@[expose] public section

namespace CAS.Cert

/-- Entry `i` of a text of entries of `w` bits, one per line. Line `i` starts at byte
`i * (w / 4 + 1)` and is `w / 4` hexadecimal digits, the most significant first, and a line
feed. The digits are read as a `w`-bit two's complement number, and the result is that number
with its sign bit flipped, the biased form of `entryVal`. The result is `none` unless `w` is a
positive multiple of 4, each of the `w / 4` bytes is a digit and the next byte is a line feed;
a byte past the end of the text is not a digit.

The loop is `Nat.rec`, which the kernel unfolds in every module; it does not unfold `Nat.fold`
in a module, since Lean's core does not expose its body. Mathlib's `CompileInductive` compiles
the recursors `Nat.rec` and `Bool.rec` for the elaborator and for a run. -/
def hexEntry? (w : Nat) (text : ByteArray) (i : Nat) : Option Nat :=
  Option.bind
    (Nat.rec (motive := fun _ ↦ Option Nat) (some 0)
      (fun d acc ↦ Option.bind acc fun a ↦
        Option.map (Nat.add (Nat.mul 16 a))
          (Sha256.hexDigit? (text.get! (Nat.add (Nat.mul i (Nat.add (Nat.div w 4) 1)) d))))
      (Nat.div w 4))
    fun v ↦
      Bool.rec none (some (Nat.xor v (Nat.shiftLeft 1 (Nat.sub w 1))))
        (Nat.blt 0 w && Nat.beq (Nat.mod w 4) 0 && Nat.beq
          (text.get! (Nat.add (Nat.mul i (Nat.add (Nat.div w 4) 1)) (Nat.div w 4))).toNat 10)

end CAS.Cert
