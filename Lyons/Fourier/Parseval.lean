/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Fourier.ZMod
import Lyons.Meta.Tag

/-!
# Parseval's identity for the discrete Fourier transform on `ZMod N`

Mathlib provides `ZMod.dft` together with the inversion formula `ZMod.dft_dft`,
but neither Parseval's identity nor the transform of a pointwise product. This
file supplies Parseval, from the orthogonality relation for `ZMod.stdAddChar`.

## The general finite abelian group

`Lyons.rateMonotonic_invExt_even` needs everything here over an arbitrary finite
abelian `A` rather than `ZMod N`, and `Lyons.Fourier.AddCharBasic` supplies it,
with the dual group `AddChar A ℂ` as the frequency domain. The load-bearing input is
`AddChar.sum_apply_eq_ite`, the general-`A` character orthogonality standing in
for `ZMod.sum_stdAddChar_mul` below; since `sum_dft_mul_conj` and
`sum_norm_sq_dft` are both derived *from* orthogonality, the arguments carry over
with the character machinery substituted underneath rather than rewritten. What
has no Mathlib counterpart in either setting is the transform of a pointwise
product (`ZMod.dft_mul` below), which the source's Lemma 2.2 needs in its
`m`-fold form.

The cyclic forms below are kept because the downstream dihedral development
consumes them.

## Main results

* `ZMod.conj_stdAddChar` : `conj (stdAddChar x) = stdAddChar (-x)`.
* `ZMod.sum_stdAddChar_mul` : orthogonality,
  `∑ k, stdAddChar (m * k) = if m = 0 then N else 0`.
* `ZMod.sum_dft_mul_conj` : the polarised identity,
  `∑ k, 𝓕 f k * conj (𝓕 g k) = N * ∑ j, f j * conj (g j)`.
* `ZMod.sum_norm_sq_dft` : Parseval,
  `∑ j, ‖f j‖ ^ 2 = (N : ℝ)⁻¹ * ∑ k, ‖𝓕 f k‖ ^ 2`.

## Implementation notes

Mathlib's transform uses the character `stdAddChar (-(j * k))`, the conjugate of
the convention `∑ j, f j * ω ^ (k * j)` used in the source paper. The two differ
by `k ↦ -k`, which leaves every statement here invariant: each is a sum over all
of `ZMod N`, and negation permutes that sum.
-/

open Finset AddChar
open scoped ComplexConjugate

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The standard additive character takes values on the unit circle, so complex
conjugation acts on it by negating the argument. -/
theorem conj_stdAddChar (x : ZMod N) :
    conj (stdAddChar x : ℂ) = stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (AddChar.norm_apply _ _)]

/-- Orthogonality for the standard additive character: summing `stdAddChar (m * k)`
over all `k` gives `N` when `m = 0`, and vanishes otherwise.

`Lyons.AddCharFourier.sum_char_apply` is the general-`A` form, which sums over
the dual group rather than, as here, over `ZMod N` for one character family. -/
theorem sum_stdAddChar_mul (m : ZMod N) :
    ∑ k : ZMod N, (stdAddChar (m * k) : ℂ) = if m = 0 then (N : ℂ) else 0 := by
  classical
  have hshift : ∀ k : ZMod N, (stdAddChar (m * k) : ℂ) = stdAddChar.mulShift m k :=
    fun k ↦ by rw [mulShift_apply]
  rw [Finset.sum_congr rfl fun k _ ↦ hshift k]
  by_cases hm : m = 0
  · subst hm
    simp [mulShift_zero, ZMod.card]
  · have hne : stdAddChar.mulShift m ≠ 1 := (isPrimitive_stdAddChar N) hm
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hne, if_neg hm]

/-- The polarised Parseval identity for `ZMod.dft`.

`Lyons.AddCharFourier.sum_dft_mul_conj` is the general-`A` form. -/
theorem sum_dft_mul_conj (f g : ZMod N → ℂ) :
    ∑ k : ZMod N, 𝓕 f k * conj (𝓕 g k)
      = (N : ℂ) * ∑ j : ZMod N, f j * conj (g j) := by
  classical
  -- Expand a single term into a double sum whose character depends only on `j' - j`.
  have expand : ∀ k : ZMod N, 𝓕 f k * conj (𝓕 g k)
      = ∑ j : ZMod N, ∑ j' : ZMod N,
          (stdAddChar ((j' - j) * k) : ℂ) * (f j * conj (g j')) := by
    intro k
    rw [dft_apply, dft_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [smul_eq_mul, smul_eq_mul, map_mul, conj_stdAddChar, neg_neg]
    have hchar : (stdAddChar (-(j * k)) : ℂ) * stdAddChar (j' * k)
        = stdAddChar ((j' - j) * k) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    calc (stdAddChar (-(j * k)) : ℂ) * f j * (stdAddChar (j' * k) * conj (g j'))
        = ((stdAddChar (-(j * k)) : ℂ) * stdAddChar (j' * k)) * (f j * conj (g j')) := by
          ring
      _ = (stdAddChar ((j' - j) * k) : ℂ) * (f j * conj (g j')) := by rw [hchar]
  rw [Finset.sum_congr rfl fun k _ ↦ expand k]
  -- Move the sum over `k` innermost.
  rw [Finset.sum_comm]
  have step : ∀ j : ZMod N,
      ∑ k : ZMod N, ∑ j' : ZMod N,
          (stdAddChar ((j' - j) * k) : ℂ) * (f j * conj (g j'))
        = ∑ j' : ZMod N, (if j' - j = 0 then (N : ℂ) else 0) * (f j * conj (g j')) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [← Finset.sum_mul, sum_stdAddChar_mul]
  rw [Finset.sum_congr rfl fun j _ ↦ step j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl]
  · intro j' _ hj'
    rw [if_neg (by simpa [sub_eq_zero] using hj'), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Parseval's identity for `ZMod.dft`, in the unnormalised convention. Mathlib
has no Parseval identity for `ZMod.dft`, so it is proved here.

`Lyons.AddCharFourier.sum_norm_sq_dft` is the general-`A` form. -/
theorem sum_norm_sq_dft (f : ZMod N → ℂ) :
    ∑ j : ZMod N, ‖f j‖ ^ 2 = (N : ℝ)⁻¹ * ∑ k : ZMod N, ‖𝓕 f k‖ ^ 2 := by
  have key := sum_dft_mul_conj f f
  have hsq : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj']; norm_cast
  simp only [hsq] at key
  have hcast : ((∑ k : ZMod N, ‖𝓕 f k‖ ^ 2 : ℝ) : ℂ)
      = ((N : ℝ) * ∑ j : ZMod N, ‖f j‖ ^ 2 : ℝ) := by push_cast at key ⊢; exact key
  have hreal : (∑ k : ZMod N, ‖𝓕 f k‖ ^ 2 : ℝ)
      = (N : ℝ) * ∑ j : ZMod N, ‖f j‖ ^ 2 := by exact_mod_cast hcast
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [hreal, inv_mul_cancel_left₀ hN]

end ZMod
