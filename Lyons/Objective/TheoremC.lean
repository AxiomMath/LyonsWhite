/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.Basic
import Lyons.Objective.Transport

/-!
# Moving the counterexample onto the dihedral group

For `p > 1` not an even integer, `(D_n, p)` fails to be rate-monotonic for a
suitable `n`, while the counterexample is constructed on the inversion extension
`G_{C,1} = InvExt (ZMod n) 0`. This file is the bridge between the two, and it is
the whole of the proof of `Lyons.not_rateMonotonic_dihedral_of_not_even` apart
from the counterexample itself
(`Lyons.Converse.exists_not_rateMonotonic_invExt`).

## The direction, which is the only subtle point

`Lyons.RateMonotonic.of_mulEquiv` is stated in one direction only:

  `(e : G ≃* H) → RateMonotonic H p → RateMonotonic G p`

and one direction serves both theorems. `Lyons.rateMonotonic_dihedral_even`
instantiates it with `G = D_n` and `H = InvExt (ZMod n) 0` along
`InvExt.dihedralEquiv.symm`, transporting an *assertion* of rate-monotonicity
onto the dihedral group. The failure has to move the other way, which is the same
lemma along the same isomorphism, contraposed: instantiating with
`G = InvExt (ZMod n) 0` and `H = D_n` along `InvExt.dihedralEquiv` itself gives

  `RateMonotonic (D_n) p → RateMonotonic (InvExt (ZMod n) 0) p`,

whose contrapositive is exactly the transport of a failure. So the positive and
negative dihedral results use `Lyons.RateMonotonic.of_mulEquiv` and
`Lyons.InvExt.dihedralEquiv` in opposite directions and neither needs a second
transport lemma. Inverting a group isomorphism is not a new obligation either —
the proof of `of_mulEquiv` already inverts one.

## Main results

* `Lyons.exists_not_rateMonotonic_dihedral_of_invExt` — the transport, in the
  existential shape `Lyons.not_rateMonotonic_dihedral_of_not_even` consumes.
-/

namespace Lyons

open InvExt

/-- **A failure of rate-monotonicity on the inversion extension of a cyclic
group transports to the dihedral group**, in the existential shape
`Lyons.not_rateMonotonic_dihedral_of_not_even` needs.

This is `Lyons.not_rateMonotonic_of_mulEquiv` along `Lyons.InvExt.dihedralEquiv`,
packaged so that `Lyons.not_rateMonotonic_dihedral_of_not_even` is this applied
to `Lyons.Converse.exists_not_rateMonotonic_invExt` and nothing further.

The `NeZero` instance travels inside the existential because `RateMonotonic`
requires the group to be a `Fintype`, and `DihedralGroup 0` is infinite
(`ZMod 0 = ℤ`); that instance is the hypothesis `n ≥ 1`. -/
theorem exists_not_rateMonotonic_dihedral_of_invExt {p : ℝ}
    (h : ∃ m : ℕ, ∃ _ : NeZero m, ¬ RateMonotonic (InvExt (ZMod m) 0) p) :
    ∃ m : ℕ, ∃ _ : NeZero m, ¬ RateMonotonic (DihedralGroup m) p := by
  obtain ⟨m, hm, hfail⟩ := h
  exact ⟨m, hm, not_rateMonotonic_of_mulEquiv (dihedralEquiv (n := m)) hfail⟩

end Lyons
