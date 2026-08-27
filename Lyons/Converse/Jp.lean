/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Lyons.Meta.Tag

/-!
# The signed power `J_p`

The failure of rate-monotonicity away from the even integers is studied through
the function `J_p(y) = |y|^(p-2) y` for `y ≠ 0`, extended by `J_p(0) = 0`.  For `p = 1` it is
the sign function, for `p = 2` it is the identity, and away from the origin it is
the derivative of `y ↦ |y|^p / p`.

The exponent is a *real* number `p ≥ 1`, so every power here is `Real.rpow`, not
a natural power.  The `y ≠ 0` case split is genuine: at `p = 1` the function is
discontinuous at the origin, which is exactly why the Riemann-sum step
`Lyons.Converse.RiemannSumAssumption` has to be assumed rather than derived from
Mathlib's box integrals.

## Main definitions

* `Lyons.Converse.signedPow` : the function `J_p`.

## Main results

* `Lyons.Converse.signedPow_neg` : `J_p` is odd.
* `Lyons.Converse.signedPow_const_mul` : `J_p` is positively homogeneous of
  degree `p - 1`.
* `Lyons.Converse.continuousAt_signedPow` : `J_p` is continuous away from the
  origin.
* `Lyons.Converse.hasDerivAt_abs_rpow_signedPow` : `s ↦ |s|^p` has derivative
  `p * J_p(y)` at every `y ≠ 0`.

Also needed to integrate `J_p ∘ cos`:
`Lyons.Converse.signedPow_eq_abs_rpow_mul_sign` removes the case split by writing
`J_p(y) = |y|^{p-1} * sign y`, from which measurability and the bound
`|J_p(y)| ≤ 1` for `|y| ≤ 1` are immediate.
-/

namespace Lyons.Converse

/-- The signed power `J_p(y) = |y|^{p-2} y` for `y ≠ 0`, and `J_p(0) = 0`.
The powers are `Real.rpow`, since `p` is real. -/
@[lyons_tag "def_Jp"]
noncomputable def signedPow (p y : ℝ) : ℝ := if y = 0 then 0 else |y| ^ (p - 2) * y

variable {p y : ℝ}

@[simp]
theorem signedPow_zero (p : ℝ) : signedPow p 0 = 0 := if_pos rfl

theorem signedPow_of_ne_zero (p : ℝ) (hy : y ≠ 0) :
    signedPow p y = |y| ^ (p - 2) * y := if_neg hy

/-- Away from the origin `J_p(y) = |y|^{p-1} * sign y`; the form used to read off
the size of `J_p`. -/
theorem signedPow_eq_rpow_sub_one_mul (hy : y ≠ 0) :
    signedPow p y = |y| ^ (p - 1) * (y / |y|) := by
  have hy' : (0 : ℝ) < |y| := abs_pos.2 hy
  rw [signedPow_of_ne_zero p hy, show p - 1 = p - 2 + 1 by ring,
    Real.rpow_add hy', Real.rpow_one]
  field_simp

/-- On the positive reals the case split disappears and `J_p(y) = y^{p-1}`. -/
theorem signedPow_of_pos (hy : 0 < y) : signedPow p y = y ^ (p - 1) := by
  rw [signedPow_of_ne_zero p hy.ne', abs_of_pos hy, show p - 1 = p - 2 + 1 by ring,
    Real.rpow_add hy, Real.rpow_one]

/-- `J_p` is odd. -/
@[lyons_tag "lem_Jp_odd"]
theorem signedPow_neg (p y : ℝ) : signedPow p (-y) = -signedPow p y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [signedPow_of_ne_zero p (neg_ne_zero.2 hy), signedPow_of_ne_zero p hy, abs_neg]
    ring

/-- `J_p` is positively homogeneous of degree `p - 1`. -/
@[lyons_tag "lem_Jp_homogeneous"]
theorem signedPow_const_mul {κ : ℝ} (hκ : 0 < κ) (p y : ℝ) :
    signedPow p (κ * y) = κ ^ (p - 1) * signedPow p y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [signedPow_of_ne_zero p (mul_ne_zero hκ.ne' hy), signedPow_of_ne_zero p hy,
      abs_mul, abs_of_pos hκ, Real.mul_rpow hκ.le (abs_nonneg y),
      show p - 1 = p - 2 + 1 by ring, Real.rpow_add hκ, Real.rpow_one]
    ring

/-- `J_p` is continuous at every nonzero point.

Continuity at the origin holds for `p > 1` and fails at `p = 1`, so the
hypothesis `y ≠ 0` is the one both cases share. -/
@[lyons_tag "lem_Jp_continuous_at"]
theorem continuousAt_signedPow (p : ℝ) (hy : y ≠ 0) : ContinuousAt (signedPow p) y := by
  have hcont : ContinuousAt (fun s : ℝ => |s| ^ (p - 2) * s) y :=
    (continuous_abs.continuousAt.rpow_const (Or.inl (by simpa using hy))).mul continuousAt_id
  refine hcont.congr (Filter.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hy) ?_)
  intro s hs
  exact (signedPow_of_ne_zero p hs).symm

/-- The function `s ↦ |s|^p` is differentiable at every `y ≠ 0`, with derivative
`p * J_p(y)`.  This is the only role `J_p` plays: it is the derivative of
`y ↦ |y|^p / p`. -/
@[lyons_tag "lem_abs_rpow_deriv"]
theorem hasDerivAt_abs_rpow_signedPow (hp : 1 ≤ p) (hy : y ≠ 0) :
    HasDerivAt (fun s : ℝ => |s| ^ p) (p * signedPow p y) y := by
  have h := (hasDerivAt_abs hy).rpow_const (p := p) (Or.inr hp)
  have hy' : (0 : ℝ) < |y| := abs_pos.2 hy
  have hsign : ((SignType.sign y : ℝ)) * |y| = y := by
    rcases hy.lt_or_gt with h' | h'
    · simp [h', abs_of_neg h']
    · simp [h', abs_of_pos h']
  refine h.congr_deriv ?_
  rw [signedPow_of_ne_zero p hy, show p - 1 = p - 2 + 1 by ring,
    Real.rpow_add hy', Real.rpow_one]
  linear_combination (p * |y| ^ (p - 2)) * hsign

/-! ### An `if`-free form, and the consequences used for integration -/

/-- `J_p(y) = |y|^{p-1} * sign y`, with no case split: at `y = 0` the right-hand
side vanishes because `Real.sign 0 = 0`, whatever `|0|^{p-1}` happens to be.
The right-hand side is a *continuous* function of `y` times a *measurable* one,
which is how `J_p ∘ cos` is shown to be integrable. -/
theorem signedPow_eq_abs_rpow_mul_sign (p y : ℝ) :
    signedPow p y = |y| ^ (p - 1) * Real.sign y := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · rw [signedPow_of_ne_zero p h.ne, Real.sign_of_neg h, abs_of_neg h,
      show p - 1 = p - 2 + 1 by ring, Real.rpow_add (by linarith), Real.rpow_one]
    ring
  · simp
  · rw [signedPow_of_pos h, Real.sign_of_pos h, abs_of_pos h, mul_one]

private theorem measurable_real_sign : Measurable Real.sign :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

/-- `J_p` is measurable for `p ≥ 1`.  Needed because `J_p ∘ cos` is
discontinuous at `p = 1` and so cannot be integrated by continuity. -/
theorem measurable_signedPow (hp : 1 ≤ p) : Measurable (signedPow p) := by
  rw [funext (signedPow_eq_abs_rpow_mul_sign p)]
  exact ((continuous_abs.rpow_const fun _ => Or.inr (by linarith)).measurable).mul
    measurable_real_sign

/-- `|J_p(y)| ≤ 1` on the closed unit interval, since `|J_p(y)| = |y|^{p-1}`
there.  This is the bound that makes `J_p ∘ cos` integrable. -/
theorem abs_signedPow_le_one (hp : 1 ≤ p) (hy : |y| ≤ 1) : |signedPow p y| ≤ 1 := by
  rw [signedPow_eq_abs_rpow_mul_sign, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) (p - 1))]
  have h1 : |y| ^ (p - 1) ≤ 1 := Real.rpow_le_one (abs_nonneg y) hy (by linarith)
  have h2 : |Real.sign y| ≤ 1 := by
    rcases Real.sign_apply_eq y with h | h | h <;> simp [h]
  calc |y| ^ (p - 1) * |Real.sign y| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **`|J_p(y)| ≤ |y|^{p-1}`** for every real `y`, with no hypothesis on `p`:
the `if`-free form `signedPow_eq_abs_rpow_mul_sign` times `|sign y| ≤ 1`.

The bound that pins `J_p` to `0` at the origin once `p > 1`, and — with `p ≥ 1`,
so that the exponent is nonnegative and `Real.rpow_le_rpow` applies — the bound
that makes `J_p` of a bounded coefficient bounded. Those are the two consumers:
`Lyons.Converse.continuous_signedPow` and the `hbound` of
`Lyons.Converse.tendsto_energy_regTestElement`. -/
theorem abs_signedPow_le_abs_rpow (p y : ℝ) : |signedPow p y| ≤ |y| ^ (p - 1) := by
  rw [signedPow_eq_abs_rpow_mul_sign, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) (p - 1))]
  have hsign : |Real.sign y| ≤ 1 := by
    rcases Real.sign_apply_eq y with h | h | h <;> simp [h]
  calc |y| ^ (p - 1) * |Real.sign y| ≤ |y| ^ (p - 1) * 1 :=
        mul_le_mul_of_nonneg_left hsign (Real.rpow_nonneg (abs_nonneg y) _)
    _ = |y| ^ (p - 1) := mul_one _

end Lyons.Converse
