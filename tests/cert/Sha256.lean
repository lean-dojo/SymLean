/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS.Cert.Sha256

/-!
# Test vectors of `CAS.Cert.Sha256`

Compiled code compares the digests of seven byte strings with the values that `sha256sum`
prints: the empty string, `abc` and a message of 56 bytes (the usual published examples of
SHA-256), 55, 64 and 119 bytes `a`, the lengths around the two places where the padding takes
one more block, and 200 bytes `a`, which are also read block by block, as a reader of a file
does. `#guard` runs compiled code, so this file is not part of the library; `tests/cert/run.sh`
elaborates it.
-/

open CAS.Cert

/-- The digest of a string, as `sha256sum` prints it. -/
def digest (s : String) : String := Sha256.hex (Sha256.hash s.toUTF8)

/-- `n` bytes `a`. -/
def letters (n : Nat) : String := String.ofList (List.replicate n 'a')

#guard digest "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard digest "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard digest "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard digest (letters 55) = "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#guard digest (letters 64) = "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
#guard digest (letters 119) = "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"

-- Block by block: two calls of `update`, each on one whole block, then `finish` on the rest.
#guard
  let data := (letters 200).toUTF8
  let state := Sha256.update (Sha256.update Sha256.initial (data.extract 0 64))
    (data.extract 64 128)
  Sha256.hex (Sha256.finish state (data.extract 128 200) 200) = digest (letters 200)
#guard digest (letters 200) = "c2a908d98f5df987ade41b5fce213067efbcc21ef2240212a41e54b5e7c28ae5"

-- The digits of a digest are read back by `hexDigit?`.
#guard (digest "abc").toUTF8.toList.map Sha256.hexDigit? |>.all (·.isSome)
#guard Sha256.hexDigit? 70 = some 15 && Sha256.hexDigit? 103 = none
