/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.Main
import Lyons.Objective.Transport

/-!
# Rate-monotonicity of the dihedral group at an even exponent

`(D_n, 2m)` is rate-monotonic.

## The derivation from the inversion-extension case, and why it needs a transport

The source deduces this from `Lyons.rateMonotonic_invExt_even` in two sentences:
take `A` cyclic of order `n` and `z` the neutral element, then `G_{A,z} = D_n`.
Here `D_n` is Mathlib's dihedral group and `G_{A,z}` is `Lyons.InvExt`, which are
two different objects, so the identification is an isomorphism
(`Lyons.InvExt.dihedralEquiv`) and the conclusion has to be transported along it
(`Lyons.RateMonotonic.of_mulEquiv`). Nothing on the path from the inversion
extension up to `Lyons.rateMonotonic_invExt_even` mentions `D_n`; the two
descriptions of the group meet here and nowhere else.

`z = 0` is the neutral element of `ZMod n`, so the standing hypothesis `z² = 1` of
the inversion extension is `0 + 0 = 0`, supplied by
`Lyons.InvExt.instFactZModZeroAddZero`.

## Main results

* `Lyons.rateMonotonic_dihedral_even` — `(D_n, 2m)` is rate-monotonic.
-/

namespace Lyons

open Finset

variable {n : ℕ} [NeZero n]

/-- **`(D_n, 2m)` is rate-monotonic.**

Raising every rate cannot increase the `ℓ^{2m}` distance of the dihedral
walk's time-`t` distribution from uniform.

Derived from `Lyons.rateMonotonic_invExt_even` at `A = ZMod n` and `z = 0`,
transported along `Lyons.InvExt.dihedralEquiv`. The two `Generating` hypotheses
are carried because the paper carries them; `Lyons.rateMonotonic_invExt_even`
does not use them, so what is proved here is stronger than what the paper
states. -/
@[lyons_tag "thm_main_forward"]
theorem rateMonotonic_dihedral_even (m : ℕ) (hm : 1 ≤ m) :
    RateMonotonic (DihedralGroup n) (2 * (m : ℝ)) :=
  RateMonotonic.of_mulEquiv (InvExt.dihedralEquiv (n := n)).symm
    (rateMonotonic_invExt_even m hm)

end Lyons
