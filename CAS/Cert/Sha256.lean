/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Init.Data.ByteArray
public import Init.Data.Array.Basic
public import Init.Data.UInt.Basic
public import Init.Data.String.Basic

/-!
# SHA-256

## Motivation

The data of a large certificate live in files outside the Lean sources. A module that embeds
such a file, and a program that reads it, must be able to say which file they mean, in a way
that anyone can compare with `sha256sum`. How is a file pinned from inside Lean, with no
external program?

## The idea

`Sha256.hash` is the function of FIPS 180-4: the message is padded to a multiple of 64 bytes
with a `0x80` byte, zeros and its length in bits, and each block of 64 bytes updates a state of
eight 32-bit words through 64 rounds. It is written as ordinary code on `UInt32` and
`ByteArray`, so compiled code runs it; it is also a total Lean function, so a proposition can
mention the digest of a byte string.

## Main results

* `Sha256.hash` (a construction): the digest of a byte string, 32 bytes.
* `Sha256.update`, `Sha256.finish`: the same computation block by block, for a reader that never
  holds the whole file; `hash` is `finish` after `update` on the whole input.
* `Sha256.hex`: a byte string as lowercase hexadecimal text, the form that `sha256sum` prints;
  `Sha256.hexDigit?`: the value of one hexadecimal digit.

Nothing is proved about the function here. Its values on seven byte strings are compared with
the digests that `sha256sum` prints, by compiled code in `tests/cert/Sha256.lean`, which
`tests/cert/run.sh` runs. Three of the strings are the usual published examples: the empty
message, `abc` and a message of 56 bytes.

## Relations

`pinned_hex%` ([Shard](Shard.lean)) compares the digest and the length of an embedded text with
the numbers written in the module. `CAS.Cert.Run.Ok` ([Run](Run.lean)) states a run of a test
on byte strings with given digests.

## Scope

A digest pins a file only as far as SHA-256 is collision resistant, which is an assumption of
cryptography and not a theorem. No statement of this library uses that assumption: a pinned file
is embedded and checked, and a run is stated existentially. The function is written with loops
that the kernel does not unfold, so a digest is computed by compiled code only; no theorem of
the library states the digest of a concrete byte string.

## References

* National Institute of Standards and Technology, *Secure Hash Standard (SHS)*, FIPS PUB 180-4,
  2015, <https://doi.org/10.6028/NIST.FIPS.180-4>. Sections 4.1.2, 4.2.2, 5.1.1, 5.3.3 and 6.2.
-/

@[expose] public section

namespace CAS.Cert.Sha256

/-- The 64 round constants, the first 32 bits of the fractional parts of the cube roots of the
first 64 primes. -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial state, the first 32 bits of the fractional parts of the square roots of the
first eight primes. -/
def initial : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotation of a 32-bit word to the right by `n` bits, for `0 < n < 32`. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The big-endian 32-bit word at byte `i` of `data`. -/
@[inline] def word (data : ByteArray) (i : Nat) : UInt32 :=
  (data.get! i).toUInt32 <<< 24 ||| (data.get! (i + 1)).toUInt32 <<< 16 |||
    (data.get! (i + 2)).toUInt32 <<< 8 ||| (data.get! (i + 3)).toUInt32

/-- One block: the state after the 64 rounds on the 64 bytes of `data` from byte `off`. -/
def compress (state : Array UInt32) (data : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  -- The message schedule.
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    w := w.push (word data (off + 4 * t))
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for t in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := h + s1 + ch + roundConstants[t]! + w[t]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d, state[4]! + e,
    state[5]! + f, state[6]! + g, state[7]! + h]

/-- The state after all whole blocks of `data` from byte `off`; the bytes after the last whole
block are not read. -/
def update (state : Array UInt32) (data : ByteArray) (off : Nat := 0) : Array UInt32 := Id.run do
  let mut st := state
  for k in [0:(data.size - off) / 64] do
    st := compress st data (off + 64 * k)
  return st

/-- The digest: `tail` holds the bytes after the last whole block (fewer than 64), `total` is
the length of the whole message in bytes. The padding is a `0x80` byte, zeros up to 56 modulo 64,
and the length in bits as a big-endian 64-bit word. -/
def finish (state : Array UInt32) (tail : ByteArray) (total : Nat) : ByteArray := Id.run do
  let mut pad := tail.push 0x80
  while pad.size % 64 != 56 do
    pad := pad.push 0
  let bits := 8 * total
  for i in [0:8] do
    pad := pad.push (UInt8.ofNat ((bits >>> (8 * (7 - i))) % 256))
  let st := update state pad
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:8] do
    let x := st[i]!
    out := (((out.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push
      x.toUInt8
  return out

/-- The SHA-256 digest of `data`, 32 bytes. -/
def hash (data : ByteArray) : ByteArray :=
  finish (update initial data) (data.extract (data.size / 64 * 64) data.size) data.size

/-- A byte string as lowercase hexadecimal text. -/
def hex (bytes : ByteArray) : String := Id.run do
  let digit (n : UInt8) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat)
  let mut out := ""
  for b in bytes do
    out := (out.push (digit (b >>> 4))).push (digit (b &&& 15))
  return out

/-- The value of an ASCII hexadecimal digit, in either case; `none` for every other byte. -/
def hexDigit? (c : UInt8) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else none

end CAS.Cert.Sha256
