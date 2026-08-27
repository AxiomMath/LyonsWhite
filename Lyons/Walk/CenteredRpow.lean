/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Lyons.GroupAlgebra.Transfer
import Lyons.Walk.Centered

/-!
# Fractional powers of the centered heat element

`(a_t^λ)^θ = a_{θt}^λ`. This is what lets the Duhamel integrand be recognised as
a *sandwich*, so it sits directly on the critical path to the main theorem.

## The bridge Mathlib cannot supply

The statement is about `cfc` applied to a matrix *exponential*, so it needs the two
to talk to each other. Mathlib has exactly that lemma —
`CFC.real_exp_eq_normedSpace_exp` — and **it is unusable here**: it requires
`NormedRing (Matrix m m ℂ)`, which exists only inside the scoped
`Matrix.Norms.Operator`, and *inside* that scope the matrix continuous functional
calculus instance is no longer found. The two hypotheses cannot be satisfied at
once. So `Lyons.cfc_exp_eq_exp` rebuilds it from the spectral theorem, using
`Matrix.IsHermitian.cfc_eq` and `Matrix.exp_units_conj` — the latter stated at
Mathlib's top level with the scope handled internally, which is what makes this
possible at all.

## Why the projection factor needs its own lemma

`a_t^λ = H_t - π_G = H_t Q` with `Q = 1 - P` a projection commuting with `H_t`.
One might hope to write `H_t Q` as `cfc g A` for the generator `A` and some `g`
vanishing at `0`. **That is false**, and quietly so: if the walk is reducible the
kernel of `A` is strictly larger than the constants, and such a `g` would send the
whole kernel to `0` where the truth is `1` on the part outside `range P`. So `Q`
must be handled as a projection, not spectrally — `Lyons.cfc_mul_proj` does that,
by Lagrange interpolation on the (finite) spectra with an interpolant forced to
vanish at `0`.

## Main results

* `Lyons.cfc_exp_eq_exp` : `cfc Real.exp A = exp A` for Hermitian `A`.
* `Lyons.cfc_rpow_exp` : `cfc (· ^ θ) (exp A) = exp (θ • A)`.
* `Lyons.cfc_mul_proj` : `cfc f (M Q) = (cfc f M) Q` when `f 0 = 0`.
* `Lyons.powElt_centeredElt` : `(a_t^λ)^θ = a_{θt}^λ`.
-/

open Matrix

namespace Lyons

/-! ### The exponential and the functional calculus -/

section Bridge

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Conjugation by a unitary passes through the exponential. -/
theorem exp_conj_unitary (u : Matrix m m ℂ) (hu : u * star u = 1) (hu' : star u * u = 1)
    (X : Matrix m m ℂ) :
    NormedSpace.exp (u * X * star u) = u * NormedSpace.exp X * star u := by
  simpa using Matrix.exp_units_conj (Units.mk u (star u) hu hu') X

/-- **The exponential is the functional calculus of `Real.exp`.**

Rebuilt from the spectral theorem because Mathlib's version needs a `NormedRing`
on matrices, which is incompatible with the matrix `cfc` instance being found —
see the module docstring. -/
theorem cfc_exp_eq_exp (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    cfc Real.exp A = NormedSpace.exp A := by
  have h1 : (hA.eigenvectorUnitary : Matrix m m ℂ)
      * star (hA.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have h2 : star (hA.eigenvectorUnitary : Matrix m m ℂ)
      * (hA.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hdiag : (diagonal (RCLike.ofReal ∘ Real.exp ∘ hA.eigenvalues) : Matrix m m ℂ)
      = diagonal (NormedSpace.exp (RCLike.ofReal ∘ hA.eigenvalues : m → ℂ)) := by
    congr 1
    funext i
    simp only [Function.comp_apply, Pi.coe_exp, RCLike.ofReal_alg]
    simp only [Complex.real_smul, mul_one]
    rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  conv_rhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [exp_conj_unitary _ h1 h2, Matrix.exp_diagonal, ← hdiag]

/-- **Fractional powers of an exponential rescale the exponent.** -/
theorem cfc_rpow_exp (A : Matrix m m ℂ) (hA : IsSelfAdjoint A) {θ : ℝ} (hθ : 0 < θ) :
    cfc (fun x : ℝ => x ^ θ) (NormedSpace.exp A) = NormedSpace.exp (θ • A) := by
  have hAh : A.IsHermitian := hA
  have hsa : IsSelfAdjoint (θ • A) := IsSelfAdjoint.smul (star_trivial θ) hA
  have hpt : ∀ x : ℝ, (Real.exp x) ^ θ = Real.exp (θ * x) := fun x => by
    rw [← Real.exp_mul, mul_comm]
  rw [← cfc_exp_eq_exp A hAh,
    ← cfc_comp (fun x : ℝ => x ^ θ) Real.exp A
      (hg := (Real.continuous_rpow_const hθ.le).continuousOn)
      (hf := Real.continuous_exp.continuousOn)]
  · rw [show ((fun x : ℝ => x ^ θ) ∘ Real.exp) = (fun x : ℝ => Real.exp (θ * x)) by
        funext x; exact hpt x]
    rw [show (fun x : ℝ => Real.exp (θ * x)) = (Real.exp ∘ fun x : ℝ => θ * x) by rfl,
      cfc_comp Real.exp (fun x : ℝ => θ * x) A, cfc_const_mul_id θ A,
      cfc_exp_eq_exp (θ • A) hsa]

/-! ### The projection factor -/

theorem mul_proj_pow (M Q : Matrix m m ℂ) (hc : Commute M Q) (hQ : Q * Q = Q) :
    ∀ n : ℕ, (M * Q) ^ (n + 1) = M ^ (n + 1) * Q := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ (a := M)]
    calc M ^ (k + 1) * Q * (M * Q) = M ^ (k + 1) * (Q * M) * Q := by noncomm_ring
      _ = M ^ (k + 1) * (M * Q) * Q := by rw [hc.symm.eq]
      _ = M ^ (k + 1) * M * (Q * Q) := by noncomm_ring
      _ = M ^ (k + 1) * M * Q := by rw [hQ]

/-- Polynomials factor through a commuting projection, up to the constant term. -/
theorem aeval_mul_proj (M Q : Matrix m m ℂ) (hc : Commute M Q) (hQ : Q * Q = Q)
    (q : Polynomial ℝ) :
    Polynomial.aeval (M * Q) q
      = (Polynomial.aeval M q) * Q + (Polynomial.coeff q 0) • ((1 : Matrix m m ℂ) - Q) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add, map_add, hp, hr, Polynomial.coeff_add, add_smul, add_mul]
    abel
  | monomial n c =>
    cases n with
    | zero => simp [Algebra.algebraMap_eq_smul_one, smul_sub]
    | succ k =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, mul_proj_pow M Q hc hQ k]
      simp [Algebra.algebraMap_eq_smul_one]

/-- **The functional calculus factors through a commuting projection**, provided
`f` vanishes at `0`.

Proved by Lagrange interpolation: the spectra are finite, so `f` agrees with a
polynomial on both of them together with `0`, and forcing the interpolant to
vanish at `0` kills the constant term that `Lyons.aeval_mul_proj` leaves behind. -/
theorem cfc_mul_proj (M Q : Matrix m m ℂ) (hM : IsSelfAdjoint M)
    (hMQ : IsSelfAdjoint (M * Q)) (hc : Commute M Q) (hQ : Q * Q = Q)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    cfc f (M * Q) = (cfc f M) * Q := by
  obtain ⟨q, hq⟩ := exists_polynomial_eqOn
    (((Matrix.finite_real_spectrum (A := M * Q)).union
      (Matrix.finite_real_spectrum (A := M))).union (Set.finite_singleton (0:ℝ))) f
  have hq0 : Polynomial.coeff q 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hq 0 (Or.inr rfl), hf0]
  rw [cfc_congr (a := M * Q) (f := f) (g := fun r => q.eval r)
      (fun r hr => (hq r (Or.inl (Or.inl hr))).symm),
    cfc_polynomial q (M * Q) hMQ, aeval_mul_proj M Q hc hQ q, hq0, zero_smul, add_zero,
    ← cfc_polynomial q M hM,
    cfc_congr (a := M) (f := fun r => q.eval r) (g := f)
      (fun r hr => hq r (Or.inl (Or.inr hr)))]

end Bridge

/-! ### The centered heat element -/

section Centered

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

set_option linter.unusedDecidableInType false in
/-- The centered element is the heat matrix times the complementary projection. -/
theorem L_centeredElt_eq_mul (lam : RateFn G) (t : ℝ) :
    L (centeredElt lam t) = heatMat lam t * (1 - L (uniform G)) := by
  rw [L_centeredElt, mul_sub, mul_one, ← L_heatElt, ← L_mul, heatElt_mul_uniform]

set_option linter.unusedDecidableInType false in
/-- **Fractional powers of the centered heat element rescale the time.** -/
@[lyons_tag "lem_centered_rpow"]
theorem powElt_centeredElt (lam : RateFn G) (t : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    powElt (centeredElt lam t) θ = centeredElt lam (θ * t) := by
  refine L_injective ?_
  rw [L_powElt _ (centeredElt_isPos lam t) hθ.le, mpow, L_centeredElt_eq_mul,
    L_centeredElt_eq_mul]
  have hQ : (1 - L (uniform G) : Matrix G G ℂ) * (1 - L (uniform G)) = 1 - L (uniform G) := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, L_uniform_mul_self]
    abel
  have hHP : heatMat lam t * L (uniform G) = L (uniform G) := by
    rw [← L_heatElt, ← L_mul, heatElt_mul_uniform]
  have hPH : L (uniform G) * heatMat lam t = L (uniform G) := by
    rw [← L_heatElt, ← L_mul, uniform_mul_heatElt]
  have hc : Commute (heatMat lam t) (1 - L (uniform G)) := by
    rw [Commute, SemiconjBy, mul_sub, sub_mul, mul_one, one_mul, hHP, hPH]
  have hM : IsSelfAdjoint (heatMat lam t) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, heatMat_conjTranspose]
  have hMQ : IsSelfAdjoint (heatMat lam t * (1 - L (uniform G))) := by
    rw [← L_centeredElt_eq_mul, IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← L_invol,
      invol_centeredElt]
  have hf0 : (fun x : ℝ => x ^ θ) 0 = 0 := Real.zero_rpow hθ.ne'
  have hgen : IsSelfAdjoint (-(t : ℂ) • L (laplacian lam)) := by
    have hL : star (L (laplacian lam)) = L (laplacian lam) := by
      rw [Matrix.star_eq_conjTranspose, ← L_invol, laplacian_invol]
    have ht : star (-(t : ℂ)) = -(t : ℂ) := by
      rw [star_neg, Complex.star_def, Complex.conj_ofReal]
    change star (-(t : ℂ) • L (laplacian lam)) = _
    rw [star_smul, ht, hL]
  have hscal : θ • (-(t : ℂ) • L (laplacian lam))
      = -((θ * t : ℝ) : ℂ) • L (laplacian lam) := by
    ext g h
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [cfc_mul_proj _ _ hM hMQ hc hQ _ hf0]
  congr 1
  rw [heatMat, heatMat, cfc_rpow_exp _ hgen hθ, hscal]

end Centered

end Lyons
