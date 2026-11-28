/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Attempt
public import CAS.Tactic.CEGA.Registry

/-!
# Built-in CEGA carrier registration

Registers the built-in checked carrier type with the extensible `cega` registry: interval
enclosure attempts (`EnclosureAttempt`, projected to an enclosure, an upper bound, an absolute
bound, or a midpoint approximation). The registration names the certificate projection and the
soundness theorems that `cega` tries before projecting. It lives apart from the carrier
definition so that the certificate layer does not import tactic code.
-/

@[expose] public section

open CAS
open CAS.Certificate
open CAS.Continuum.RationalInterval

attribute [cega_carrier enclosureAttempt EnclosureAttempt.cert
  [
    EnclosureAttempt.boundOn,
    EnclosureAttempt.boundOn_abs,
    EnclosureAttempt.approxOn_center]]
  EnclosureAttempt
