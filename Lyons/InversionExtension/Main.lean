/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.ReflectionStep
import Lyons.InversionExtension.Rotation
import Lyons.Objective.RateMonotonic
import Lyons.Walk.OrbitInduction

/-!
# Every inversion extension is rate-monotonic at an even exponent

`Lyons.rateMonotonic_invExt_even` is assembled from the abelian-part step
(`Lyons.Phi_addOrbit_rot_le`) and the outside step
(`Lyons.Phi_addOrbit_refl_le`).

## One orbit at a time

`InvExt.sumEquiv` says every element of `G_{A,z}` is `ι a` or `ι d τ`, which in
the concrete model is the two constructors, so the one-orbit step is a case split
and nothing more. Because the reflection inequality and the outside rate family
are stated at every `d ∈ A`, the second case is a rewriting of definitions: no
relabelling automorphism, and no invariance of the transition function or of the
power sum under one, is needed.

## The induction

`Lyons.Phi_le_of_le_of_step` is the group-generic interpolation; all this file
supplies is the one-orbit step.

## From the power sum to rate-monotonicity

`Lyons.Phi` is `∑_g (p_t^ν(g) - |G|⁻¹)^{2m}`, and `2m` is even, so it is the inner
sum of `Lyons.distToUniform` at `p = 2m`. Both sides are nonnegative and
`y ↦ y^{1/(2m)}` is nondecreasing on `[0, ∞)`, so taking `(2m)`-th roots preserves
the inequality. The two `Generating` hypotheses are carried because the paper
carries them, and are not used.

## Main results

* `Lyons.Phi_addOrbit_le` : raising the rate on one inverse orbit does not
  increase the power sum.
* `Lyons.Phi_le_of_le` : raising every rate does not increase the power sum.
* `Lyons.rateMonotonic_invExt_even` : `(G_{A,z}, 2m)` is rate-monotonic.
-/

open Finset

namespace Lyons

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {z : A}
  [Fact (z + z = 0)]

set_option linter.unusedDecidableInType false in
/-- **Raising the rate on one inverse orbit does not increase the power sum.** -/
@[lyons_tag "lem_single_orbit_step"]
theorem Phi_addOrbit_le (lam : RateFn (InvExt A z)) {s : InvExt A z} (hs1 : s ≠ 1)
    {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m := by
  cases s with
  | rot a =>
    -- inside the abelian part the increment is central; no Duhamel formula needed
    exact Phi_addOrbit_rot_le lam a hs1 hc ht m
  | refl d =>
    -- outside it, the whole sandwich apparatus is consumed
    exact Phi_addOrbit_refl_le lam d hc ht hm

set_option linter.unusedDecidableInType false in
/-- The one-orbit step, packaged for `Lyons.Phi_le_of_le_of_step`. -/
theorem oneOrbitStep_invExt {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    OneOrbitStep (InvExt A z) t m :=
  fun lam _ hs1 _ hc => Phi_addOrbit_le lam hs1 hc ht hm

set_option linter.unusedDecidableInType false in
/-- **Increasing every rate does not increase the power sum.** -/
@[lyons_tag "lem_orbit_induction"]
theorem Phi_le_of_le (lam mu : RateFn (InvExt A z))
    (hle : ∀ g : InvExt A z, g ≠ 1 → lam g ≤ mu g) {t : ℝ} (ht : 0 ≤ t) {m : ℕ}
    (hm : 1 ≤ m) : Phi mu t m ≤ Phi lam t m :=
  Phi_le_of_le_of_step (oneOrbitStep_invExt ht hm) lam mu hle

set_option linter.unusedDecidableInType false in
/-- **`(G_{A,z}, 2m)` is rate-monotonic.**

Raising every rate cannot increase the `ℓ^{2m}` distance of the walk on the
inversion extension from uniform, for every finite abelian `A` and every `z ∈ A`
with `z² = 1`. -/
@[lyons_tag "thm_main_general"]
theorem rateMonotonic_invExt_even (m : ℕ) (hm : 1 ≤ m) :
    RateMonotonic (InvExt A z) (2 * (m : ℝ)) := by
  intro lam mu hlam hmu _ _ hle t ht
  have key : Phi hmu.toRateFn t m ≤ Phi hlam.toRateFn t m :=
    Phi_le_of_le hlam.toRateFn hmu.toRateFn
      (fun g hg => by
        rw [IsSymmRate.toRateFn_apply, IsSymmRate.toRateFn_apply, if_neg hg, if_neg hg]
        exact hle g) ht hm
  have hexp : (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  have hPhi : ∀ nu : RateFn (InvExt A z),
      Phi nu t m = ∑ g : InvExt A z,
        |heatCoeffReal nu t g - (Fintype.card (InvExt A z) : ℝ)⁻¹| ^ (2 * m) := by
    intro nu
    rw [Phi_eq_sum_real]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [centeredHeatCoeffReal, pow_mul, ← sq_abs, ← pow_mul]
  unfold distToUniform
  rw [hexp]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  simp only [Real.rpow_natCast]
  rw [← hPhi, ← hPhi]
  exact key

end Lyons
