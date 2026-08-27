/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Moments
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ZMod.Basic

/-!
# A negative exponential sum, conditionally on Riemann-sum convergence

For real `p ≥ 1` which is not a positive even integer there are odd `K ≥ 3` and
odd `n > 2K` with

  `∑_{j ∈ ℤ/n} J_p(cos(2πj/n)) cos(2πKj/n) < 0`.

This is proved here under one explicit hypothesis, `RiemannSumAssumption p`: that
the uniform left-endpoint Riemann sums of `t ↦ J_p(cos t) cos(Kt)` over `[0, 2π]`
converge to its mean.  At `p = 1` the integrand is `sgn(cos t) cos(Kt)`, which is
discontinuous, and Mathlib packages no uniform-Riemann-sum statement in the shape
needed; for `p > 1` the integrand is continuous and the hypothesis is derivable
from Mathlib's box integrals.  Every other ingredient of the argument is proved
unconditionally, so the sum estimate follows from
`Lyons.Converse.exists_neg_char_sum_of_riemann` as soon as
`RiemannSumAssumption p` is available.

## Main definitions

* `Lyons.Converse.RiemannSumAssumption` : convergence of the uniform
  left-endpoint Riemann sums of `t ↦ J_p(cos t) cos(Kt)` to its mean, at every
  frequency.

## Main results

* `Lyons.Converse.exists_neg_char_sum_of_riemann` : the negative exponential sum,
  under that assumption.

## Implementation notes

Oddness of `n` is encoded by writing `n = 2l + 1`, which also supplies the
`NeZero` instance that `∑ j : ZMod n` needs — an existentially quantified `n`
cannot carry one.
-/

namespace Lyons.Converse

open Filter Finset Real

/-- A sum over `{0, …, n-1}` as a sum over `ℤ/n`, along `ZMod.val`. -/
private theorem sum_range_eq_sum_zmod {n : ℕ} [NeZero n] (g : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, g j = ∑ q : ZMod n, g q.val :=
  Finset.sum_nbij' (i := fun j => (j : ZMod n)) (j := fun q : ZMod n => q.val)
    (fun _ _ => Finset.mem_univ _) (fun q _ => Finset.mem_range.2 (ZMod.val_lt q))
    (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha))
    (fun q _ => ZMod.natCast_zmod_val q)
    (fun a ha => by rw [ZMod.val_cast_of_lt (Finset.mem_range.1 ha)])

/-- **Riemann-sum convergence for the integrand of this file.**  The uniform
left-endpoint Riemann sums of `t ↦ J_p(cos t) cos(Kt)` over `[0, 2π]` converge to
its mean `Γ_K(p)`, for every frequency `K`.

This is an assumption, not a theorem: at `p = 1` the integrand is
`sgn(cos t) cos(Kt)`, bounded and Riemann integrable but discontinuous at `π/2`
and `3π/2`, and Mathlib has no statement identifying the mesh-to-zero limit of
uniform left-endpoint sums for such an integrand.  For `p > 1` the integrand is
continuous and the statement is derivable from Mathlib's box integrals; the
`p = 1` sliver is what is genuinely assumed. -/
def RiemannSumAssumption (p : ℝ) : Prop :=
  ∀ K : ℤ, Tendsto
    (fun N : ℕ => (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
      signedPow p (Real.cos (2 * π * (j : ℝ) / N))
        * Real.cos ((K : ℝ) * (2 * π * (j : ℝ) / N)))
    atTop (nhds (signedPowFourier p K))

variable {p : ℝ}

/-- **A negative exponential sum**, under the Riemann-sum assumption.

The frequency is `K = 2m + 3` with `m` the largest integer with `2m ≤ p`; the
hypothesis that `p` is not a positive even integer is what makes `2m < p` strict,
and `Γ_K(p) < 0` is then `Lyons.Converse.signedPowFourier_neg`.  A sequence with
a negative limit is
eventually negative, so the Riemann sums at all large `n` are negative, and `n`
is chosen odd and larger than `2K` among those. -/
theorem exists_neg_char_sum_of_riemann (hp : 1 ≤ p)
    (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * m) (hR : RiemannSumAssumption p) :
    ∃ K l : ℕ, Odd K ∧ 3 ≤ K ∧ 2 * K < 2 * l + 1 ∧
      ∑ j : ZMod (2 * l + 1),
          signedPow p (Real.cos (2 * π * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ)))
            * Real.cos (2 * π * ((K : ℝ) * (j.val : ℝ)) / ((2 * l + 1 : ℕ) : ℝ)) < 0 := by
  -- `m` is the largest integer with `2m ≤ p`.
  set m : ℕ := ⌊p / 2⌋₊ with hm
  have hub : p < 2 * (m : ℝ) + 2 := by
    have h := Nat.lt_floor_add_one (p / 2)
    rw [← hm] at h
    linarith
  have hle : 2 * (m : ℝ) ≤ p := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ p / 2 by linarith)
    rw [← hm] at h
    linarith
  have hlb : 2 * (m : ℝ) < p := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, Nat.cast_zero]
      linarith
    · exact hle.lt_of_ne (hp2 m hpos).symm
  -- `Γ_K(p) < 0` at `K = 2m + 3`.
  have hgamma : signedPowFourier p (2 * (m : ℤ) + 3) < 0 := signedPowFourier_neg hp hlb hub
  -- So the Riemann sums are eventually negative.
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp ((hR (2 * (m : ℤ) + 3)).eventually_lt_const hgamma)
  refine ⟨2 * m + 3, N₀ + 2 * m + 3, ⟨m + 1, by ring⟩, by omega, by omega, ?_⟩
  -- An average is negative only if the sum is.
  have hdiv : ∀ (N : ℕ) (S : ℝ), 0 < N → (1 / (N : ℝ)) * S < 0 → S < 0 := by
    intro N S hN h
    by_contra hcon
    rw [not_lt] at hcon
    have hpos : (0 : ℝ) < 1 / (N : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
      positivity
    nlinarith [mul_nonneg hpos.le hcon]
  have hSneg := hdiv _ _ (by omega) (hN₀ (2 * (N₀ + 2 * m + 3) + 1) (by omega))
  -- Pass from `{0, …, n-1}` to `ℤ/n` and match the frequency.
  refine lt_of_le_of_lt (le_of_eq ?_) hSneg
  rw [sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 2
  push_cast
  ring

end Lyons.Converse
