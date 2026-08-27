/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Lyons.GroupAlgebra.Basic

/-!
# Right translations and the commutant of the left regular representation

The left regular representation of `ℝ[G]` is characterised, inside all of
`Matrix G G ℂ`, by commuting with every right translation. This is the
mechanism by which the group algebra is shown closed under operations defined
on matrices — notably the continuous functional calculus, whose output commutes
with everything the input commutes with (`Commute.cfc_real`), hence with every
right translation, hence is again a left convolution.

## Main results

* `Lyons.R` : the right-translation matrix.
* `Lyons.L_commutes_R` : left convolutions commute with right translations.
* `Lyons.commutes_R_iff` : a matrix commutes with every right translation iff
  its entries depend only on `g * g'⁻¹`, i.e. iff it is a left convolution.
-/

open Matrix

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Right translation by `h`, as a `G × G` matrix: it sends the basis vector at
`g` to the one at `g * h`. -/
@[lyons_tag "def_right_translation"]
def R (h : G) : Matrix G G ℂ :=
  Matrix.of fun g g' => if g' = g * h then 1 else 0

omit [Fintype G] in
@[simp] theorem R_apply (h g g' : G) : R h g g' = if g' = g * h then 1 else 0 := rfl

/-- Right multiplication by `R h` shifts the column index by `h⁻¹`. -/
theorem mul_R_apply (T : Matrix G G ℂ) (h g g' : G) :
    (T * R h) g g' = T g (g' * h⁻¹) := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (g' * h⁻¹)]
  · rw [R_apply, if_pos (by group), mul_one]
  · intro u _ hu
    rw [R_apply, if_neg (fun hcon => hu (by rw [hcon]; group)), mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- Left multiplication by `R h` shifts the row index by `h`. -/
theorem R_mul_apply (T : Matrix G G ℂ) (h g g' : G) :
    (R h * T) g g' = T (g * h) g' := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (g * h)]
  · rw [R_apply, if_pos rfl, one_mul]
  · intro u _ hu
    rw [R_apply, if_neg hu, zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- Left convolutions commute with right translations. -/
@[lyons_tag "lem_L_commutes_R"]
theorem L_commutes_R (x : MonoidAlgebra ℝ G) (h : G) : L x * R h = R h * L x := by
  ext g g'
  rw [mul_R_apply, R_mul_apply, L_apply, L_apply]
  have hgrp : g * (g' * h⁻¹)⁻¹ = g * h * g'⁻¹ := by group
  rw [hgrp]

/-- **The commutant of the right translations.** A matrix commutes with every
right translation exactly when its entries depend only on `g * g'⁻¹` — that is,
exactly when it is a left convolution operator.

Stated as this entrywise condition rather than as `∃ z, T = L z` on purpose:
`L` here has *real* coefficients, while a general `T` satisfying the hypothesis
need not, so an existence form over `ℝ[G]` would be false as stated and an
existence form over `ℂ[G]` would require a parallel complex-coefficient
development. The entrywise form carries the same content, is what the
downstream argument consumes, and commits to neither. -/
@[lyons_tag "lem_commutant"]
theorem commutes_R_iff (T : Matrix G G ℂ) :
    (∀ h, T * R h = R h * T) ↔ ∀ g g', T g g' = T (g * g'⁻¹) 1 := by
  constructor
  · intro hcomm g g'
    -- Take `h = g'` and read off the `(g, g')` entry.
    have := congrFun (congrFun (hcomm g') (g * g'⁻¹)) g'
    rw [mul_R_apply, R_mul_apply] at this
    simpa using this.symm
  · intro hT h
    ext g g'
    rw [mul_R_apply, R_mul_apply, hT g (g' * h⁻¹), hT (g * h) g']
    have hgrp : g * (g' * h⁻¹)⁻¹ = g * h * g'⁻¹ := by group
    rw [hgrp]

omit [Fintype G] [DecidableEq G] in
/-- The entries of a left convolution matrix are determined by its first column,
which is the corresponding coefficient function. -/
theorem L_apply_one (x : MonoidAlgebra ℝ G) (g : G) :
    L x g 1 = ((co x g : ℝ) : ℂ) := by
  rw [L_apply, inv_one, mul_one]

/-- **The functional calculus does not leave the group algebra.** Applied to a
left convolution `L x`, any continuous-functional-calculus image `cfc f (L x)` is
again a left convolution: its entries depend only on `g * g'⁻¹`. This is where
`commutes_R_iff` earns its keep.

The classical route writes spectral projections as polynomials in `L x` by
Lagrange interpolation and then passes to a limit; Mathlib's `Commute.cfc_real`
supplies the commutation directly, so neither step is needed. -/
@[lyons_tag "lem_rpow_mem"]
theorem cfc_L_conv (x : MonoidAlgebra ℝ G) (f : ℝ → ℝ) (g g' : G) :
    cfc f (L x) g g' = cfc f (L x) (g * g'⁻¹) 1 :=
  (commutes_R_iff _).mp
    (fun h => Commute.cfc_real (show Commute (L x) (R h) from L_commutes_R x h) f) g g'


end Lyons
