/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Lyons.Walk.Kolmogorov

/-!
# Duhamel's formula

The derivative of `α ↦ e^{-t(A + αB)}` when `A` and `B` do **not** commute —
which is the whole reason the reflection half of the main theorem is hard, and
the rotation half is not.

## Structure of the proof

Two steps, and the first is the substantial one.

`Lyons.duhamel_identity` is an exact, `ε`-free statement:

`e^{-tA'} - e^{-tA} = -∫₀ᵗ e^{-sA'} (A' - A) e^{-(t-s)A} ds`,

for *any* two matrices. It is the fundamental theorem of calculus applied to the
interpolating path `s ↦ e^{-sA'} e^{-(t-s)A}`, whose derivative collapses to a
single term because `A'` commutes with its own exponential. No commutation between
`A` and `A'`, no positivity, and no self-adjointness is used anywhere.

`Lyons.duhamel_deriv` then takes the limit. With `A' = A + aB` and `A = A + αB`
the difference `A' - A` is exactly `(a - α) • B`, so the identity computes the
*slope* of the exponential in the parameter on the nose
(`Lyons.slope_exp_param`) — no error term to estimate. The derivative is then
continuity of a parametric interval integral, which Mathlib supplies as
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.

## Two notational points

`e^{-(t-s)A}` is written `exp ((s - t) • A)`, the same matrix with one fewer
negation to carry through the sign bookkeeping.

`Matrix.Norms.Operator` must be open: `NormedSpace.exp`'s derivative and
continuity lemmas all need the `NormedRing` instance it provides, and the
interval integral needs the `NormedAddCommGroup`.

## Main results

* `Lyons.duhamel_identity` : the exact integral identity.
* `Lyons.duhamel_deriv` : Duhamel's formula.
-/

open Matrix
open scoped Norms.Operator

namespace Lyons

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### Differentiating the two factors of the interpolating path -/

theorem hasDerivAt_exp_neg_smul (A : Matrix m m ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • A))
      (-(NormedSpace.exp ((-s) • A) * A)) s := by
  have hinner : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := (hasDerivAt_id s).neg
  have h := (hasDerivAt_exp_smul A (-s)).scomp s hinner
  rwa [neg_one_smul] at h

theorem hasDerivAt_exp_sub_smul (A : Matrix m m ℂ) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u - t) • A))
      (NormedSpace.exp ((s - t) • A) * A) s := by
  have hinner : HasDerivAt (fun u : ℝ => u - t) (1 : ℝ) s := (hasDerivAt_id s).sub_const t
  have h := (hasDerivAt_exp_smul A (s - t)).scomp s hinner
  rwa [one_smul] at h

/-- **The interpolating path's derivative collapses to one term.**

The product rule gives two, and they combine because `A` commutes with
`exp ((s - t) • A)` — which is the only commutation fact the whole development
needs here. -/
theorem hasDerivAt_duhamelPath (A A' : Matrix m m ℂ) (t s : ℝ) :
    HasDerivAt
      (fun u : ℝ => NormedSpace.exp ((-u) • A') * NormedSpace.exp ((u - t) • A))
      (-(NormedSpace.exp ((-s) • A') * (A' - A)
        * NormedSpace.exp ((s - t) • A))) s := by
  have h1 := hasDerivAt_exp_neg_smul A' s
  have h2 := hasDerivAt_exp_sub_smul A t s
  have h := HasDerivAt.mul h1 h2
  have hcomm : NormedSpace.exp ((s - t) • A) * A = A * NormedSpace.exp ((s - t) • A) :=
    (((Commute.refl A).smul_left (s - t)).exp_left).eq
  rw [hcomm] at h
  have hval : -(NormedSpace.exp ((-s) • A') * (A' - A) * NormedSpace.exp ((s - t) • A))
      = -(NormedSpace.exp ((-s) • A') * A') * NormedSpace.exp ((s - t) • A)
        + NormedSpace.exp ((-s) • A') * (A * NormedSpace.exp ((s - t) • A)) := by
    noncomm_ring
  rw [hval]
  exact h

/-! ### The exact identity -/

/-- **Duhamel's identity.** The difference of two matrix exponentials as an
integral over the interpolating path. Exact, with no `ε` and no limit. -/
theorem duhamel_identity (A A' : Matrix m m ℂ) (t : ℝ) :
    NormedSpace.exp ((-t) • A') - NormedSpace.exp ((-t) • A)
      = -∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • A') * (A' - A)
          * NormedSpace.exp ((s - t) • A) := by
  have hc1 : Continuous fun s : ℝ => NormedSpace.exp ((-s) • A') :=
    NormedSpace.exp_continuous.comp (by fun_prop)
  have hc2 : Continuous fun s : ℝ => NormedSpace.exp ((s - t) • A) :=
    NormedSpace.exp_continuous.comp (by fun_prop)
  have hcont : Continuous fun s : ℝ =>
      -(NormedSpace.exp ((-s) • A') * (A' - A) * NormedSpace.exp ((s - t) • A)) :=
    ((hc1.mul continuous_const).mul hc2).neg
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_duhamelPath A A' t s) (hcont.intervalIntegrable 0 t)
  simp only [sub_self, zero_smul, NormedSpace.exp_zero, mul_one, neg_zero, zero_sub,
    one_mul] at hint
  rw [← hint]
  exact intervalIntegral.integral_neg

/-! ### The derivative in the parameter -/

/-- **The slope of the exponential in its parameter, exactly.**

Because the two generators differ by exactly `(a - α) • B`, the identity's
integrand is `(a - α)` times something, and the factor cancels the slope's
denominator. There is no error term to estimate — the only limit left is the
continuity of a parametric integral. -/
theorem slope_exp_param (A B : Matrix m m ℂ) (t α : ℝ) {a : ℝ} (ha : a ≠ α) :
    slope (fun c : ℝ => NormedSpace.exp ((-t) • (A + c • B))) α a
      = -∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • (A + a • B)) * B
          * NormedSpace.exp ((s - t) • (A + α • B)) := by
  have hsub : (A + a • B) - (A + α • B) = (a - α) • B := by
    rw [add_sub_add_left_eq_sub, sub_smul]
  rw [slope_def_module, duhamel_identity (A + α • B) (A + a • B) t]
  have hne : (a - α) ≠ 0 := sub_ne_zero_of_ne ha
  have hsmul : ∀ s : ℝ, NormedSpace.exp ((-s) • (A + a • B)) * ((A + a • B) - (A + α • B))
      * NormedSpace.exp ((s - t) • (A + α • B))
      = (a - α) • (NormedSpace.exp ((-s) • (A + a • B)) * B
          * NormedSpace.exp ((s - t) • (A + α • B))) := by
    intro s
    rw [hsub, mul_smul_comm, smul_mul_assoc]
  rw [intervalIntegral.integral_congr
      (g := fun s => (a - α) • (NormedSpace.exp ((-s) • (A + a • B)) * B
        * NormedSpace.exp ((s - t) • (A + α • B)))) (fun s _ => hsmul s),
    intervalIntegral.integral_smul, smul_neg, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- **Duhamel's formula.**

`A` and `B` need not commute; that is the point. When they do, the integrand is
constant in `s` and this reduces to the elementary product rule — which is exactly
why the rotation branch of the main theorem needs none of this. -/
@[lyons_tag "lem_duhamel"]
theorem duhamel_deriv (A B : Matrix m m ℂ) (t α : ℝ) :
    HasDerivAt (fun a : ℝ => NormedSpace.exp ((-t) • (A + a • B)))
      (-∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • (A + α • B)) * B
          * NormedSpace.exp ((s - t) • (A + α • B))) α := by
  have hjoint : Continuous (Function.uncurry fun (a : ℝ) (s : ℝ) =>
      NormedSpace.exp ((-s) • (A + a • B)) * B
        * NormedSpace.exp ((s - t) • (A + α • B))) := by
    unfold Function.uncurry
    have h1 : Continuous fun p : ℝ × ℝ => NormedSpace.exp ((-p.2) • (A + p.1 • B)) :=
      NormedSpace.exp_continuous.comp (by fun_prop)
    have h2 : Continuous fun p : ℝ × ℝ => NormedSpace.exp ((p.2 - t) • (A + α • B)) :=
      NormedSpace.exp_continuous.comp (by fun_prop)
    exact (h1.mul continuous_const).mul h2
  have hcont : Continuous fun a : ℝ => -∫ s in (0:ℝ)..t,
      NormedSpace.exp ((-s) • (A + a • B)) * B
        * NormedSpace.exp ((s - t) • (A + α • B)) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint 0 t).neg
  refine hasDerivAt_iff_tendsto_slope.mpr ?_
  refine Filter.Tendsto.congr' ?_ ((hcont.tendsto α).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (slope_exp_param A B t α ha).symm

end Lyons
