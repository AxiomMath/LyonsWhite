/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.ConverseCyclic
import Lyons.InversionExtension.Main
import Lyons.Objective.TheoremA

/-! # Satisfying the formal challenge -/

open Finset

namespace Challenge

open Lyons

/-- **`thm_main_forward` — Theorem A.** For all positive integers `n` and `m`,
raising every rate cannot increase the `ℓ^{2m}` distance of the dihedral walk's
time-`t` distribution from uniform. -/
theorem thm_main_forward (n : ℕ) [NeZero n] (m : ℕ) (hm : 1 ≤ m) :
    RateMonotonic (DihedralGroup n) (2 * (m : ℝ)) :=
  rateMonotonic_dihedral_even m hm

/-- **`thm_main_general` — Theorem B.** The same holds over every inversion
extension of a finite abelian group by an involution. -/
theorem thm_main_general {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (z : A) [Fact (z + z = 0)] (m : ℕ) (hm : 1 ≤ m) :
    RateMonotonic (InvExt A z) (2 * (m : ℝ)) :=
  rateMonotonic_invExt_even m hm

/-- **`thm_main_converse` — Theorem C.** For every real `p > 1` that is not an
even integer, there is an `n` for which the pair `(D_n, p)` is not
rate-monotonic. -/
theorem thm_main_converse (p : ℝ) (hp : 1 < p)
    (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * (m : ℝ)) :
    ∃ n : ℕ, ∃ _ : NeZero n, ¬ RateMonotonic (DihedralGroup n) p :=
  not_rateMonotonic_dihedral_of_not_even hp hp2

end Challenge
