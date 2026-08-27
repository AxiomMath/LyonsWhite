/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.CharSum
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform left-endpoint Riemann sums of a continuous function

This file proves that for a continuous `f : ℝ → ℝ` the uniform left-endpoint
Riemann sums over `[0, 1]`,

  `(1/N) ∑_{j < N} f(j/N)`,

converge to `∫_0^1 f`, rescales that to `[0, 2π]`, and uses the rescaled form to
**discharge** `Lyons.Converse.RiemannSumAssumption p` for every `p > 1`.

## Main results

* `Lyons.Analysis.riemannSum_tendsto_integral` : the Riemann-sum convergence on
  `[0, 1]` for continuous integrands.
* `Lyons.Analysis.riemannSum_tendsto_integral_two_pi` : the same statement
  rescaled to `[0, 2π]`, which is the shape
  `Lyons.Converse.RiemannSumAssumption` is stated in.
* `Lyons.Converse.continuous_signedPow` : `J_p` is continuous on all of `ℝ` when
  `1 < p`.  This strengthens `Lyons.Converse.continuousAt_signedPow`, which
  excludes the origin, under the extra hypothesis `1 < p`.
* `Lyons.Converse.riemannSumAssumption_of_one_lt` : the development's only
  assumption, `Lyons.Converse.RiemannSumAssumption p`, holds for `1 < p`.

## Implementation notes

The proof of `riemannSum_tendsto_integral` is the classical modulus-of-continuity
argument, not a specialisation of Mathlib's `BoxIntegral` theory: Mathlib packages
no one-dimensional statement about uniform partitions with left-endpoint tags.
The integral is split along the partition with
`intervalIntegral.sum_integral_adjacent_intervals`, the Riemann sum is rewritten
as the same sum of integrals of *constants*, and the two are compared term by
term with `intervalIntegral.norm_integral_le_of_norm_le_const`.

The `1 < p` in the last two results is used in exactly one place: continuity of
`J_p` at the origin, where `|J_p(y)| = |y|^{p-1} → 0` iff `p > 1`.  At `p = 1`
the integrand `J_p ∘ cos` is the sign of the cosine, which jumps at `π/2` and
`3π/2`; the continuous Riemann-sum theorem does not apply there, so that single
exponent is not covered.
-/

namespace Lyons.Analysis

open MeasureTheory

/-- The one-step estimate behind `riemannSum_tendsto_integral`: if `ε` is a
modulus of continuity of `f` on `[0, 1]` at scale `δ`, and the mesh `1/N` is at
most `δ`, then the `N`-th left-endpoint Riemann sum is within `ε` of the
integral.

The hypothesis is phrased with `≤` on both sides so that
`Metric.uniformContinuousOn_iff_le` can supply it verbatim. -/
private theorem abs_riemannSum_sub_integral_le {f : ℝ → ℝ} (hf : Continuous f) {ε δ : ℝ}
    (hmod : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| ≤ δ → |f x - f y| ≤ ε)
    {N : ℕ} (hN : 0 < N) (hNδ : 1 / (N : ℝ) ≤ δ) :
    |(1 / (N : ℝ)) * ∑ j ∈ Finset.range N, f ((j : ℝ) / (N : ℝ)) - ∫ t in (0 : ℝ)..1, f t| ≤ ε := by
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  -- The mesh of the `j`-th subinterval.
  have hdiff : ∀ j : ℕ, ((j : ℝ) + 1) / (N : ℝ) - (j : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
    intro j; field_simp; ring
  -- Step 1: split `∫_0^1` along the partition `j ↦ j/N`.
  have hsplit : ∑ j ∈ Finset.range N, ∫ t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), f t
      = ∫ t in (0 : ℝ)..1, f t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) / (N : ℝ)) (n := N) (μ := volume) (f := f)
      fun k _ => hf.intervalIntegrable _ _
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hNne] using h
  -- Step 2: the Riemann sum is the same sum of integrals, of constants.
  have hriem : (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, f ((j : ℝ) / (N : ℝ))
      = ∑ j ∈ Finset.range N,
          ∫ _t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), f ((j : ℝ) / (N : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const, hdiff j, smul_eq_mul]
  -- Step 3: subtract term by term.
  rw [hriem, ← hsplit, ← Finset.sum_sub_distrib]
  have hterm : ∀ j : ℕ,
      (∫ _t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), f ((j : ℝ) / (N : ℝ)))
          - ∫ t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), f t
        = ∫ t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), (f ((j : ℝ) / (N : ℝ)) - f t) :=
    fun j => (intervalIntegral.integral_sub (intervalIntegrable_const)
      (hf.intervalIntegrable _ _)).symm
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  -- Step 4: each term is at most `ε/N`, and there are `N` of them.
  have hle : ∀ j ∈ Finset.range N,
      |∫ t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), (f ((j : ℝ) / (N : ℝ)) - f t)|
        ≤ ε * (1 / (N : ℝ)) := by
    intro j hj
    have hj1 : (j : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hj)
    have hmesh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hab : (j : ℝ) / (N : ℝ) ≤ ((j : ℝ) + 1) / (N : ℝ) := by
      have := hdiff j; linarith
    have hlo : (0 : ℝ) ≤ (j : ℝ) / (N : ℝ) := by positivity
    have hhi : ((j : ℝ) + 1) / (N : ℝ) ≤ 1 := (div_le_one hNR).2 hj1
    have hbnd : ∀ t ∈ Set.uIoc ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ)),
        ‖f ((j : ℝ) / (N : ℝ)) - f t‖ ≤ ε := by
      intro t ht
      rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
      rw [Real.norm_eq_abs]
      refine hmod _ (Set.mem_Icc.2 ⟨hlo, hab.trans hhi⟩) _
        (Set.mem_Icc.2 ⟨hlo.trans ht.1.le, ht.2.trans hhi⟩) ?_
      rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - (j : ℝ) / (N : ℝ))]
      have := hdiff j
      linarith [ht.2]
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbnd).trans ?_
    rw [hdiff j, abs_of_nonneg hmesh.le]
  calc |∑ j ∈ Finset.range N,
          ∫ t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), (f ((j : ℝ) / (N : ℝ)) - f t)|
      ≤ ∑ j ∈ Finset.range N,
          |∫ t in ((j : ℝ) / (N : ℝ))..(((j : ℝ) + 1) / (N : ℝ)), (f ((j : ℝ) / (N : ℝ)) - f t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range N, ε * (1 / (N : ℝ)) := Finset.sum_le_sum hle
    _ = ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- **Uniform left-endpoint Riemann sums of a continuous function converge to its
integral**, on `[0, 1]`.

Mathlib's `BoxIntegral` theory does contain the general Riemann integral, but no
packaged one-dimensional statement about uniform partitions with left-endpoint
tags, so this is proved directly from the modulus of continuity of `f` on the
compact interval `[0, 1]`. -/
theorem riemannSum_tendsto_integral (f : ℝ → ℝ) (hf : Continuous f) :
    Filter.Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, f ((j : ℝ) / (N : ℝ)))
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, f t)) := by
  have hUC : UniformContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff_le.1 hUC (ε / 2) (by linarith)
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℕ, 0 < M ∧ 1 / (M : ℝ) < δ := by
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ
    exact ⟨M + 1, M.succ_pos, by push_cast; exact hM⟩
  refine ⟨M, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le hM0 hN
  have hNδ : 1 / (N : ℝ) ≤ δ :=
    (one_div_le_one_div_of_le (Nat.cast_pos.mpr hM0) (by exact_mod_cast hN)).trans hM.le
  have hmod : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ δ → |f x - f y| ≤ ε / 2 := fun x hx y hy hxy => by
    simpa only [Real.dist_eq] using hδ' x hx y hy (by rwa [Real.dist_eq])
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_riemannSum_sub_integral_le hf hmod hNpos hNδ) (by linarith)

/-- **Uniform left-endpoint Riemann sums of a continuous function converge to its
mean**, on `[0, 2π]`: the `[0, 1]` statement `riemannSum_tendsto_integral`
rescaled by `t = 2π s`.

Continuity of `f` is essential and not merely convenient: for an integrand that
is only bounded, with a jump inside `[0, 2π]`, the uniform left-endpoint sums
need not converge to the mean. Downstream this excludes exactly the exponent
`p = 1`, where `J_p ∘ cos` is discontinuous. -/
@[lyons_tag "lem_ext_riemann_sum"]
theorem riemannSum_tendsto_integral_two_pi (f : ℝ → ℝ) (hf : Continuous f) :
    Filter.Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
        f (2 * Real.pi * (j : ℝ) / (N : ℝ)))
      Filter.atTop (nhds ((1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), f t)) := by
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  have h := riemannSum_tendsto_integral (fun s => f (2 * Real.pi * s))
    (hf.comp (continuous_const.mul continuous_id))
  have hint : (∫ s in (0 : ℝ)..1, f (2 * Real.pi * s))
      = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), f t := by
    rw [intervalIntegral.integral_comp_mul_left f hπ, smul_eq_mul, mul_zero, mul_one, one_div]
  rw [hint] at h
  refine h.congr fun N => ?_
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc])

end Lyons.Analysis

namespace Lyons.Converse

variable {p : ℝ}

/-- **`J_p` is continuous on all of `ℝ` when `p > 1`.**

Away from the origin this is `continuousAt_signedPow`, which needs no hypothesis
on `p`.  At the origin is where `1 < p` is genuinely used: `|J_p(y)| ≤ |y|^{p-1}`
tends to `0` exactly when `p - 1 > 0`, and at `p = 1` the function is the sign
function, which jumps. -/
theorem continuous_signedPow (hp : 1 < p) : Continuous (signedPow p) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · rw [ContinuousAt, signedPow_zero]
    refine squeeze_zero_norm' (a := fun z : ℝ => |z| ^ (p - 1))
      (Filter.Eventually.of_forall fun z => ?_) ?_
    · rw [Real.norm_eq_abs]; exact abs_signedPow_le_abs_rpow p z
    · exact Filter.Tendsto.rpow_const_nhds_zero
        (by simpa using continuous_abs.tendsto (0 : ℝ)) (by linarith)
  · exact continuousAt_signedPow p hy

/-- **The development's only assumption holds for every `p > 1`.**

`RiemannSumAssumption p` asks that the uniform left-endpoint Riemann sums of
`t ↦ J_p(cos t) cos(Kt)` over `[0, 2π]` converge to its mean `Γ_K(p)`.  For
`p > 1` the integrand is continuous, by `continuous_signedPow`, so this is the
continuous Riemann-sum theorem `Lyons.Analysis.riemannSum_tendsto_integral_two_pi`
applied to it, the limit being `signedPowFourier` by definition.

Composed with `exists_neg_char_sum_of_riemann` this gives
`Lyons.Converse.exists_neg_char_sum` below. -/
theorem riemannSumAssumption_of_one_lt (hp : 1 < p) : RiemannSumAssumption p := by
  intro K
  have hcont : Continuous fun t : ℝ =>
      signedPow p (Real.cos t) * Real.cos ((K : ℝ) * t) :=
    ((continuous_signedPow hp).comp Real.continuous_cos).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  exact Lyons.Analysis.riemannSum_tendsto_integral_two_pi _ hcont

/-- **A negative exponential sum.**

This is `Lyons.Converse.exists_neg_char_sum_of_riemann` with its Riemann-sum
hypothesis discharged by `riemannSumAssumption_of_one_lt`, so the statement is
unconditional.

The exponent `p = 1` is **not** covered, and is not claimed anywhere: there
`J_p(cos t) = sgn(cos t)`, discontinuous at `π/2` and `3π/2`, and the continuous
Riemann-sum theorem this rests on does not apply. `p = 1` is the `ℓ¹` metric,
twice total variation, so the gap is a real one and remains open. -/
@[lyons_tag "lem_neg_char_sum"]
theorem exists_neg_char_sum (hp : 1 < p) (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * m) :
    ∃ K l : ℕ, Odd K ∧ 3 ≤ K ∧ 2 * K < 2 * l + 1 ∧
      ∑ j : ZMod (2 * l + 1),
          signedPow p (Real.cos (2 * Real.pi * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ)))
            * Real.cos (2 * Real.pi * ((K : ℝ) * (j.val : ℝ))
                / ((2 * l + 1 : ℕ) : ℝ)) < 0 :=
  exists_neg_char_sum_of_riemann hp.le hp2 (riemannSumAssumption_of_one_lt hp)

end Lyons.Converse
