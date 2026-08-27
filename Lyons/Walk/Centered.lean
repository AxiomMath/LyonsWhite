/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Heat

/-!
# The centered heat element is positive

The object the main theorem is about is `a_t^λ = h_t^λ - π_G`, and everything
downstream — fractional powers, the sandwich, the reflection inequality — needs
it to be positive.

## The argument, and why it is three lines

No decomposition of the space of column vectors into the range and the kernel of
`P = L_{π_G}` is needed: absorption gives `HP = PH = P`, from which
`(1 - P) H (1 - P) = H - P` by four rewrites, and `1 - P` is self-adjoint. So
`H - P` is a `*`-conjugate of `H`, and `H` is positive because it is the
exponential of a self-adjoint matrix. Mathlib's
`Matrix.PosSemidef.mul_mul_conjTranspose_same` then closes it.

## Main definitions

* `Lyons.centeredElt` : `a_t^λ`, defined as `h_t^λ - π_G`.

## Main results

* `Lyons.heatMat_posSemidef` : the heat matrix is positive.
* `Lyons.centeredElt_isPos` : `a_t^λ ⪰ 0`.
* `Lyons.invol_centeredElt` : `a_t^λ` is self-adjoint.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### The heat matrix is positive -/

set_option linter.unusedDecidableInType false in
/-- The heat matrix is self-adjoint: the conjugate transpose passes through the
exponential, and the generator is self-adjoint. -/
theorem heatMat_conjTranspose (lam : RateFn G) (t : ℝ) :
    (heatMat lam t)ᴴ = heatMat lam t := by
  simp only [heatMat]
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
    ← L_invol, laplacian_invol, star_neg, Complex.star_def, Complex.conj_ofReal]

set_option linter.unusedDecidableInType false in
/-- The heat matrix at time `t` is the square of the one at `t / 2`. -/
theorem heatMat_half (lam : RateFn G) (t : ℝ) :
    heatMat lam t = heatMat lam (t / 2) * heatMat lam (t / 2) := by
  simp only [heatMat]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
  congr 2
  push_cast
  ring

omit [Group G] in
/-- **The exponential of a self-adjoint matrix is positive semidefinite.**

Not via Mathlib's `IsSelfAdjoint.exp_nonneg`, and the reason is not that it is
missing but that its two hypotheses cannot be satisfied at once on matrices: it
is stated for a star-ordered ring, so it needs the `NormedRing` structure that
lives only in the scoped `Matrix.Norms.Operator`, and *inside* that scope the
matrix continuous functional calculus instance is no longer found. Opening the
scope loses the hypothesis; not opening it loses the conclusion.

Factoring `e^A = e^{A/2} e^{A/2}` with `e^{A/2}` self-adjoint exhibits it as
`Bᴴ B` and needs no norm at all: `Matrix.exp_conjTranspose` and
`Matrix.exp_add_of_commute` are both stated at Mathlib's top level. -/
@[lyons_tag "lem_ext_exp_psd"]
theorem exp_posSemidef {A : Matrix G G ℂ} (hA : IsSelfAdjoint A) :
    (NormedSpace.exp A).PosSemidef := by
  set B := ((2 : ℂ)⁻¹) • A with hB
  have hAh : Aᴴ = A := by rw [← Matrix.star_eq_conjTranspose]; exact hA
  have hBh : Bᴴ = B := by
    rw [hB, Matrix.conjTranspose_smul, hAh]
    congr 1
    simp
  have hsum : B + B = A := by rw [hB, ← add_smul]; norm_num
  have h : NormedSpace.exp A = (NormedSpace.exp B)ᴴ * NormedSpace.exp B := by
    rw [← Matrix.exp_conjTranspose, hBh,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl _), hsum]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

set_option linter.unusedDecidableInType false in
/-- **The heat matrix is positive.** `Lyons.exp_posSemidef` at the generator. -/
theorem heatMat_posSemidef (lam : RateFn G) (t : ℝ) : (heatMat lam t).PosSemidef := by
  rw [heatMat]
  refine exp_posSemidef ?_
  have hL : star (L (laplacian lam)) = L (laplacian lam) := by
    rw [Matrix.star_eq_conjTranspose, ← L_invol, laplacian_invol]
  have ht : star (-(t : ℂ)) = -(t : ℂ) := by
    rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  change star (-(t : ℂ) • L (laplacian lam)) = _
  rw [star_smul, ht, hL]

set_option linter.unusedDecidableInType false in
theorem heatMat_nonneg (lam : RateFn G) (t : ℝ) :
    (0 : Matrix G G ℂ) ≤ heatMat lam t :=
  Matrix.nonneg_iff_posSemidef.mpr (heatMat_posSemidef lam t)

/-! ### The uniform projection -/

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- The uniform element is self-adjoint: every coefficient is the same. -/
@[simp] theorem invol_uniform : invol (uniform G) = uniform G := by
  refine co_injective fun g ↦ ?_
  rw [co_invol, coe_uniform, coe_uniform]

set_option linter.unusedDecidableInType false in
/-- `P = L_{π_G}` is self-adjoint. -/
theorem L_uniform_conjTranspose : (L (uniform G))ᴴ = L (uniform G) := by
  rw [← L_invol, invol_uniform]

set_option linter.unusedDecidableInType false in
/-- `P` is idempotent. -/
theorem L_uniform_mul_self : L (uniform G) * L (uniform G) = L (uniform G) := by
  rw [← L_mul, uniform_idem]

/-! ### The centered heat element -/

/-- **The centered heat element** `a_t^λ = h_t^λ - π_G`.

Defined as the difference of two group-algebra elements rather than from the
coefficient function, so that the algebra identities below are available without
any coefficient bookkeeping; `Lyons.co_centeredElt` records that its coefficients
are the centered transition function. -/
noncomputable def centeredElt (lam : RateFn G) (t : ℝ) : MonoidAlgebra ℝ G :=
  heatElt lam t - uniform G

set_option linter.unusedDecidableInType false in
@[simp] theorem co_centeredElt (lam : RateFn G) (t : ℝ) (g : G) :
    co (centeredElt lam t) g = centeredHeatCoeffReal lam t g := by
  rw [centeredElt, co_sub, co_heatElt, coe_uniform, centeredHeatCoeffReal]

theorem L_centeredElt (lam : RateFn G) (t : ℝ) :
    L (centeredElt lam t) = heatMat lam t - L (uniform G) := by
  rw [centeredElt, L_sub, L_heatElt]

/-- The key algebraic identity: `H - P` is a `*`-conjugate of `H` by `1 - P`. -/
theorem heatMat_sub_uniform_eq (lam : RateFn G) (t : ℝ) :
    heatMat lam t - L (uniform G)
      = (1 - L (uniform G)) * heatMat lam t * (1 - L (uniform G))ᴴ := by
  have hPH : L (uniform G) * heatMat lam t = L (uniform G) := by
    rw [← L_heatElt, ← L_mul, uniform_mul_heatElt]
  have hHP : heatMat lam t * L (uniform G) = L (uniform G) := by
    rw [← L_heatElt, ← L_mul, heatElt_mul_uniform]
  have hQ : (1 - L (uniform G) : Matrix G G ℂ)ᴴ = 1 - L (uniform G) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, L_uniform_conjTranspose]
  rw [hQ, sub_mul, one_mul, hPH, mul_sub, mul_one, sub_mul, hHP, L_uniform_mul_self]
  abel

/-- **The centered heat element is positive.** -/
@[lyons_tag "lem_centered_pos"]
theorem centeredElt_isPos (lam : RateFn G) (t : ℝ) : IsPos (centeredElt lam t) := by
  rw [IsPos, L_centeredElt, heatMat_sub_uniform_eq]
  exact (heatMat_posSemidef lam t).mul_mul_conjTranspose_same _

/-- **The centered heat element is self-adjoint.** Positivity already contains
it, since positivity is defined through a positive semidefinite — hence
Hermitian — matrix. -/
@[lyons_tag "lem_centered_selfadjoint"]
theorem invol_centeredElt (lam : RateFn G) (t : ℝ) :
    invol (centeredElt lam t) = centeredElt lam t :=
  (centeredElt_isPos lam t).invol_eq

end Lyons
