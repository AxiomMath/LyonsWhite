/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.GroupAlgebra.Commutant

/-!
# Entrywise conjugation, and realness of functional-calculus images

`Lyons.cfc_L_conv` shows that a functional-calculus image of `L x` is again a
left convolution — its entries are determined by the first column. To read a
group-algebra element off that column one also needs the entries to be **real**,
and that is what this file supplies.

## The mechanism

Entrywise complex conjugation is an `ℝ`-algebra star endomorphism of
`Matrix G G ℂ` (`Lyons.conjHom`), and it is continuous. Mathlib's
`StarAlgHomClass.map_cfc` therefore lets it pass through the continuous
functional calculus. Since `L x` has real entries it is fixed by conjugation, so
`cfc f (L x)` is fixed too — which is exactly realness of its entries.

This replaces the route through uniqueness of the positive square root, which
Mathlib does not appear to provide for matrices.

## Main results

* `Lyons.conjHom` : entrywise conjugation, bundled.
* `Lyons.continuous_conjHom` : it is continuous — needed because `fun_prop`
  cannot see a locally-defined map, so `map_cfc`'s side condition must be
  discharged by hand.
* `Lyons.conjHom_cfc_L` : conjugation fixes `cfc f (L x)`.
* `Lyons.cfc_L_im_eq_zero` : the entries of `cfc f (L x)` are real.
-/

open Matrix

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Entrywise complex conjugation, as an `ℝ`-algebra star endomorphism of the
matrix algebra. It is `ℝ`-linear but not `ℂ`-linear, which is why the scalars
must be `ℝ` here. -/
noncomputable def conjHom : Matrix G G ℂ →⋆ₐ[ℝ] Matrix G G ℂ where
  toFun M := M.map (starRingEnd ℂ)
  map_one' := by ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' M N := by ext i j; simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp
  commutes' r := by
    ext i j
    by_cases h : i = j <;>
      simp [Algebra.algebraMap_eq_smul_one, h]
  map_star' M := by ext i j; simp

omit [Group G] in
@[simp] theorem conjHom_apply (M : Matrix G G ℂ) (i j : G) :
    conjHom M i j = (starRingEnd ℂ) (M i j) := rfl

omit [Group G] in
/-- `conjHom` is continuous. Supplied explicitly because `fun_prop` cannot
discharge `map_cfc`'s continuity side condition for a map defined here. -/
theorem continuous_conjHom :
    Continuous (conjHom : Matrix G G ℂ → Matrix G G ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))

/-- The left regular representation has real entries, so conjugation fixes it. -/
@[simp] theorem conjHom_L (x : MonoidAlgebra ℝ G) : conjHom (L x) = L x := by
  ext g h
  simp [L_apply]

/-- **Conjugation passes through the functional calculus, and fixes
`cfc f (L x)`.** -/
theorem conjHom_cfc_L (x : MonoidAlgebra ℝ G) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (L x))) (hx : IsSelfAdjoint (L x)) :
    conjHom (cfc f (L x)) = cfc f (L x) := by
  rw [StarAlgHomClass.map_cfc conjHom f (L x) (hφ := continuous_conjHom), conjHom_L]

/-- **The entries of `cfc f (L x)` are real.** This is what lets a group-algebra
element be reconstructed from the first column. -/
@[lyons_tag "lem_cfc_real"]
theorem cfc_L_im_eq_zero (x : MonoidAlgebra ℝ G) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (L x))) (hx : IsSelfAdjoint (L x))
    (g h : G) : (cfc f (L x) g h).im = 0 := by
  have := congrFun (congrFun (conjHom_cfc_L x f hf hx) g) h
  rw [conjHom_apply, starRingEnd_apply] at this
  exact Complex.conj_eq_iff_im.mp this

end Lyons
