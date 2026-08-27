/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Fourier.Parseval

/-!
# The finite even-exponent Fourier majorant inequality

If `u` has a nonnegative-real Fourier transform dominating that of `f`
pointwise, then `‖f‖_{2m} ≤ ‖u‖_{2m}` for every positive integer `m`. This is
the elementary positive half of the Hardy–Littlewood majorant principle,
available precisely because the exponent is an even integer:
`‖f‖_{2m}^{2m} = ‖f ^ m‖_2^2`, so Parseval applies to the pointwise power.

This is the one point at which the source paper's argument needs the exponent to
be an even integer; the rest of it works for every real `p ≥ 1`.

## Main results

* `ZMod.dconv` : cyclic convolution in the Fourier variable.
* `ZMod.dft_mul` : the product formula, `N * 𝓕 (f * g) k = dconv (𝓕 f) (𝓕 g) k`.
* `ZMod.dft_pow_dominated` : the induction on `m`, carrying both the domination
  of `𝓕 (f ^ m)` and the nonneg-realness of `𝓕 (u ^ m)`.
* `ZMod.sum_norm_pow_le` : the majorant inequality.
-/

open Finset
open scoped ComplexConjugate

namespace ZMod

variable {N : ℕ} [NeZero N]

/-! ### Nonnegative-real values

`z = (‖z‖ : ℂ)` says exactly that `z` is a nonnegative real. Closure under
products and sums is what the induction below needs. -/

private theorem nonnegReal_mul {z w : ℂ} (hz : z = (‖z‖ : ℂ)) (hw : w = (‖w‖ : ℂ)) :
    z * w = (‖z * w‖ : ℂ) := by
  rw [norm_mul]
  push_cast
  rw [← hz, ← hw]

private theorem nonnegReal_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ)
    (hF : ∀ i ∈ s, F i = (‖F i‖ : ℂ)) :
    ∑ i ∈ s, F i = (‖∑ i ∈ s, F i‖ : ℂ) := by
  have hcast : ∑ i ∈ s, F i = ((∑ i ∈ s, ‖F i‖ : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl hF
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]

/-- Cyclic convolution in the Fourier variable. -/
@[lyons_tag "def_conv"]
noncomputable def dconv (F H : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => ∑ l : ZMod N, F l * H (k - l)

/-- The transform of a pointwise product is the normalised convolution of the
transforms. Mathlib supplies `ZMod.dft` but no product formula for it.

`Lyons.AddCharFourier.dft_mul` is the general-`A` form, whose convolution runs
over the dual group. -/
theorem dft_mul (f g : ZMod N → ℂ) (k : ZMod N) :
    (N : ℂ) * 𝓕 (f * g) k = dconv (𝓕 f) (𝓕 g) k := by
  classical
  -- Expand each convolution term into a double sum, isolating the `l`-character.
  have expand : ∀ l : ZMod N, 𝓕 f l * 𝓕 g (k - l)
      = ∑ j : ZMod N, ∑ j' : ZMod N,
          (stdAddChar ((j' - j) * l) : ℂ) *
            ((stdAddChar (-(j' * k)) : ℂ) * (f j * g j')) := by
    intro l
    rw [dft_apply, dft_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [smul_eq_mul, smul_eq_mul]
    have hchar : (stdAddChar (-(j * l)) : ℂ) * stdAddChar (-(j' * (k - l)))
        = (stdAddChar ((j' - j) * l) : ℂ) * (stdAddChar (-(j' * k)) : ℂ) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    calc (stdAddChar (-(j * l)) : ℂ) * f j *
            ((stdAddChar (-(j' * (k - l))) : ℂ) * g j')
        = ((stdAddChar (-(j * l)) : ℂ) * stdAddChar (-(j' * (k - l)))) *
            (f j * g j') := by ring
      _ = ((stdAddChar ((j' - j) * l) : ℂ) * (stdAddChar (-(j' * k)) : ℂ)) *
            (f j * g j') := by rw [hchar]
      _ = _ := by ring
  unfold dconv
  rw [Finset.sum_congr rfl fun l _ ↦ expand l, Finset.sum_comm]
  have step : ∀ j : ZMod N,
      ∑ l : ZMod N, ∑ j' : ZMod N,
          (stdAddChar ((j' - j) * l) : ℂ) *
            ((stdAddChar (-(j' * k)) : ℂ) * (f j * g j'))
        = ∑ j' : ZMod N, (if j' - j = 0 then (N : ℂ) else 0) *
            ((stdAddChar (-(j' * k)) : ℂ) * (f j * g j')) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [← Finset.sum_mul, sum_stdAddChar_mul]
  rw [Finset.sum_congr rfl fun j _ ↦ step j]
  -- Only the diagonal `j' = j` survives.
  rw [dft_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl, smul_eq_mul]
    simp only [Pi.mul_apply]
  · intro j' _ hj'
    rw [if_neg (by simpa [sub_eq_zero] using hj'), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The inductive heart of the majorant argument: domination of the transforms
is inherited by pointwise powers, and the majorant's transform stays a
nonnegative real. The two conclusions are proved together because the induction
step needs nonneg-realness at `m` to identify a sum of moduli with the modulus
of a sum; neither half is available on its own. -/
@[lyons_tag "lem_dft_pow"]
theorem dft_pow_dominated (f u : ZMod N → ℂ)
    (hu : ∀ k, 𝓕 u k = (‖𝓕 u k‖ : ℂ))
    (hfu : ∀ k, ‖𝓕 f k‖ ≤ ‖𝓕 u k‖) (m : ℕ) (hm : 1 ≤ m) :
    (∀ k, ‖𝓕 (f ^ m) k‖ ≤ ‖𝓕 (u ^ m) k‖) ∧
      (∀ k, 𝓕 (u ^ m) k = (‖𝓕 (u ^ m) k‖ : ℂ)) := by
  classical
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  induction m, hm using Nat.le_induction with
  | base => simpa using ⟨hfu, hu⟩
  | succ m hm ih =>
    obtain ⟨ihdom, ihpos⟩ := ih
    -- Rewrite `𝓕 (· ^ (m+1))` through the product formula.
    have key : ∀ (h : ZMod N → ℂ) (k : ZMod N),
        (N : ℂ) * 𝓕 (h ^ (m + 1)) k = dconv (𝓕 (h ^ m)) (𝓕 h) k := by
      intro h k
      have : h ^ (m + 1) = h ^ m * h := by ring
      rw [this, dft_mul]
    -- Nonneg-realness of the majorant's transform at `m + 1`.
    have hposSucc : ∀ k, 𝓕 (u ^ (m + 1)) k = (‖𝓕 (u ^ (m + 1)) k‖ : ℂ) := by
      intro k
      have hterms : ∀ l ∈ (univ : Finset (ZMod N)),
          𝓕 (u ^ m) l * 𝓕 u (k - l) = (‖𝓕 (u ^ m) l * 𝓕 u (k - l)‖ : ℂ) :=
        fun l _ ↦ nonnegReal_mul (ihpos l) (hu (k - l))
      have hconv : dconv (𝓕 (u ^ m)) (𝓕 u) k
          = (‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ : ℂ) := by
        unfold dconv
        exact nonnegReal_sum _ _ hterms
      have hmul := key u k
      -- `𝓕 (u ^ (m+1)) k = N⁻¹ * (a nonnegative real)`.
      have hsplit : 𝓕 (u ^ (m + 1)) k = (N : ℂ)⁻¹ * dconv (𝓕 (u ^ m)) (𝓕 u) k := by
        rw [← hmul]
        field_simp
      rw [hsplit, hconv, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      push_cast
      ring
    refine ⟨fun k ↦ ?_, hposSucc⟩
    -- Domination at `m + 1`, via the triangle inequality on the convolution.
    have hfk := key f k
    have huk := key u k
    have hbound : ‖dconv (𝓕 (f ^ m)) (𝓕 f) k‖ ≤ ‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ := by
      have hle : ‖dconv (𝓕 (f ^ m)) (𝓕 f) k‖
          ≤ ∑ l : ZMod N, ‖𝓕 (u ^ m) l‖ * ‖𝓕 u (k - l)‖ := by
        unfold dconv
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
        rw [norm_mul]
        exact mul_le_mul (ihdom l) (hfu (k - l)) (norm_nonneg _) (norm_nonneg _)
      have heq : ∑ l : ZMod N, ‖𝓕 (u ^ m) l‖ * ‖𝓕 u (k - l)‖
          = ‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ := by
        have hterms : ∀ l ∈ (univ : Finset (ZMod N)),
            𝓕 (u ^ m) l * 𝓕 u (k - l) = (‖𝓕 (u ^ m) l * 𝓕 u (k - l)‖ : ℂ) :=
          fun l _ ↦ nonnegReal_mul (ihpos l) (hu (k - l))
        have hconv : dconv (𝓕 (u ^ m)) (𝓕 u) k
            = (‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ : ℂ) := by
          unfold dconv
          exact nonnegReal_sum _ _ hterms
        have : ((∑ l : ZMod N, ‖𝓕 (u ^ m) l‖ * ‖𝓕 u (k - l)‖ : ℝ) : ℂ)
            = ((‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ : ℝ) : ℂ) := by
          rw [← hconv]
          unfold dconv
          push_cast
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          rw [← ihpos l, ← hu (k - l)]
        exact_mod_cast this
      exact hle.trans_eq heq
    -- Divide the bound by `N`.
    have hfnorm : ‖𝓕 (f ^ (m + 1)) k‖
        = (N : ℝ)⁻¹ * ‖dconv (𝓕 (f ^ m)) (𝓕 f) k‖ := by
      have h1 : (N : ℝ) * ‖𝓕 (f ^ (m + 1)) k‖
          = ‖dconv (𝓕 (f ^ m)) (𝓕 f) k‖ := by
        rw [← hfk, norm_mul, Complex.norm_natCast]
      rw [← h1]
      field_simp
    have hunorm : ‖𝓕 (u ^ (m + 1)) k‖
        = (N : ℝ)⁻¹ * ‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ := by
      have h1 : (N : ℝ) * ‖𝓕 (u ^ (m + 1)) k‖
          = ‖dconv (𝓕 (u ^ m)) (𝓕 u) k‖ := by
        rw [← huk, norm_mul, Complex.norm_natCast]
      rw [← h1]
      field_simp
    rw [hfnorm, hunorm]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- **The finite even-exponent majorant inequality.** If each `𝓕 u k` is a
nonnegative real dominating `‖𝓕 f k‖`, then `‖f‖_{2m} ≤ ‖u‖_{2m}`.

`Lyons.AddCharFourier.sum_pow_le_of_dft_le` is the general-`A` form. -/
theorem sum_norm_pow_le (f u : ZMod N → ℂ)
    (hu : ∀ k, 𝓕 u k = (‖𝓕 u k‖ : ℂ))
    (hfu : ∀ k, ‖𝓕 f k‖ ≤ ‖𝓕 u k‖) {m : ℕ} (hm : 1 ≤ m) :
    ∑ j : ZMod N, ‖f j‖ ^ (2 * m) ≤ ∑ j : ZMod N, ‖u j‖ ^ (2 * m) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hdom, -⟩ := dft_pow_dominated f u hu hfu m hm
  -- `∑ ‖h j‖ ^ (2m) = ∑ ‖(h ^ m) j‖ ^ 2`: this is where evenness is used.
  have hsplit : ∀ h : ZMod N → ℂ,
      ∑ j : ZMod N, ‖h j‖ ^ (2 * m) = ∑ j : ZMod N, ‖(h ^ m) j‖ ^ 2 := by
    intro h
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Pi.pow_apply, norm_pow, ← pow_mul, mul_comm m 2]
  rw [hsplit f, hsplit u, sum_norm_sq_dft (f ^ m), sum_norm_sq_dft (u ^ m)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_) (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (hdom k) 2

end ZMod
