/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Sandwich
import Lyons.Walk.ReflectionDeriv

/-!
# The power sum along a one-orbit rate family

The integral bookkeeping behind the reflection step, for a general finite group
and a general inverse orbit.
This is the half of the main theorem the whole Duhamel/sandwich apparatus was
built for; the reflection inequality itself is taken as a hypothesis (`key`), so
that nothing here depends on the shape of the group.

## The closed interval, and why the endpoints are not a nuisance

`Lyons.hasDerivAt_reflCentered_integral` writes its integrand with `reflHeatMat` at
the scaled times `θt` and `(1-θ)t`, not as a sandwich: the sandwich
form fails at `θ = 0` and `θ = 1`, where `a_α^0` is `1` rather than `1 - P`. One
might expect the consumer to pay for that with an almost-everywhere argument. It
does not: `Lyons.reflHeatMat_sandwich` shows the two *products* agree at the
endpoints as well, because the discrepancy is a multiple of `P` and `L a_α`
annihilates `P` on either side. So the pointwise inequality is available on all of
`Set.Icc 0 1` and `intervalIntegral.integral_mono_on` applies directly.

## Why the rate family is re-parametrised

`RateFn.addOrbit` takes `0 ≤ α` as a proof argument, so
`α ↦ Φ_m(λ ⊕_s α, t)` is not a function of `α` and cannot be differentiated as
written. `Lyons.reflPhi` is the total version, built on `Lyons.reflLap`, and
`Lyons.reflPhi_eq` identifies it with `Lyons.Phi` wherever `α ≥ 0`. The
differentiation happens on the total family; only the final statement is in terms
of `Phi`.

The family used here is `RateFn.addOrbit`, which *adds* on the orbit, rather than
`RateFn.setOrb`, which overwrites: `addOrbit` needs no side condition on the base
rate, so `Lyons.reflPhi_eq` holds unconditionally. The two agree by
`Lyons.RateFn.setOrb_eq_addOrbit`, applied once by the consumer.

## The exponents `2m` and `2m-1`

Truncated natural subtraction in an exponent is a liability, so the sign statement
is indexed by `p` with `m = p + 1`, matching the reflection inequality's `2p+1` /
`2p+2`. `Lyons.antitoneOn_reflPhi` converts back to `1 ≤ m`.

## Main results

* `Lyons.reflHeatMat_sandwich` : the Duhamel integrand is the sandwich, endpoints
  included.
* `Lyons.reflPhi`, `Lyons.reflPhi_eq` : the power sum, total in the rate.
* `Lyons.hasDerivAt_reflPhi` : its derivative, from the chain rule.
* `Lyons.sum_reflCentCo_pow_mul_deriv_nonpos` : the derivative is nonpositive,
  given the reflection inequality at every element of the orbit.
* `Lyons.antitoneOn_reflPhi`, `Lyons.Phi_addOrbit_le_of_key` : the reflection
  step, modulo the reflection inequality.
-/

open Matrix Finset
open scoped Norms.Operator MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Absorption on the right -/

set_option linter.unusedDecidableInType false in
theorem single_mul_uniform (b : G) :
    MonoidAlgebra.single b (1 : ℝ) * uniform G = uniform G := by
  classical
  rw [uniform_absorb]
  have h : ∑ g : G, co (MonoidAlgebra.single b (1 : ℝ)) g = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · intro hcon; exact absurd (Finset.mem_univ b) hcon
  rw [h, one_smul]

set_option linter.unusedDecidableInType false in
theorem L_single_mul_L_uniform (b : G) :
    L (MonoidAlgebra.single b (1 : ℝ)) * L (uniform G) = L (uniform G) := by
  rw [← L_mul, single_mul_uniform]

set_option linter.unusedDecidableInType false in
theorem centeredElt_mul_uniform (lam : RateFn G) (t : ℝ) :
    centeredElt lam t * uniform G = 0 := by
  rw [centeredElt, sub_mul, heatElt_mul_uniform, uniform_idem, sub_self]

set_option linter.unusedDecidableInType false in
theorem uniform_mul_centeredElt (lam : RateFn G) (t : ℝ) :
    uniform G * centeredElt lam t = 0 := by
  rw [centeredElt, mul_sub, uniform_mul_heatElt, uniform_idem, sub_self]

/-! ### The functional calculus at the two endpoints -/

omit [Group G] in
theorem mpow_zero {M : Matrix G G ℂ} (hM : IsSelfAdjoint M) : mpow M 0 = 1 := by
  rw [mpow, show (fun t : ℝ => t ^ (0 : ℝ)) = (fun _ : ℝ => (1 : ℝ)) from
    funext fun t => Real.rpow_zero t, cfc_const (1 : ℝ) M hM, map_one]

omit [Group G] in
theorem mpow_one {M : Matrix G G ℂ} (hM : IsSelfAdjoint M) : mpow M 1 = M := by
  rw [mpow, show (fun t : ℝ => t ^ (1 : ℝ)) = (id : ℝ → ℝ) from
    funext fun t => Real.rpow_one t, cfc_id ℝ M hM]

/-! ### The Duhamel integrand is the sandwich, endpoints included -/

set_option linter.unusedDecidableInType false in
theorem L_uniform_mul_L_centeredElt (lam : RateFn G) (t : ℝ) :
    L (uniform G) * L (centeredElt lam t) = 0 := by
  rw [← L_mul, uniform_mul_centeredElt, L_zero]

set_option linter.unusedDecidableInType false in
theorem L_centeredElt_mul_L_uniform (lam : RateFn G) (t : ℝ) :
    L (centeredElt lam t) * L (uniform G) = 0 := by
  rw [← L_mul, centeredElt_mul_uniform, L_zero]

theorem reflHeatMat_zero (lam0 : RateFn G) (s : G) (α : ℝ) :
    reflHeatMat lam0 s 0 α = 1 := by
  rw [reflHeatMat, neg_zero, zero_smul, NormedSpace.exp_zero]

theorem isSelfAdjoint_L_centeredElt (lam : RateFn G) (t : ℝ) :
    IsSelfAdjoint (L (centeredElt lam t)) :=
  (Matrix.nonneg_iff_posSemidef.mp ((isPos_iff_le _).mp (centeredElt_isPos lam t))).isHermitian

set_option linter.unusedDecidableInType false in
/-- **The Duhamel integrand is the sandwich, for every `θ ∈ [0,1]`.**

At `θ = 0` and `θ = 1` the two sides' *factors* differ — `a_α^0 = 1`, not `1 - P` —
yet the products agree, because the discrepancy is a multiple of `P` and `P` is
annihilated by `L a_α` on either side. That is what lets the consumer stay on the
closed interval and avoid an almost-everywhere argument.

The generator is indexed by `s`, the sandwiched element by `x`; they are
unrelated, which is what lets the orbit sum be taken termwise. -/
theorem reflHeatMat_sandwich (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) (x : G) (t : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (reflHeatMat lam0 s (θ * t) α * (1 - L (uniform G)))
        * L (MonoidAlgebra.single x (1 : ℝ))
        * (reflHeatMat lam0 s ((1 - θ) * t) α * (1 - L (uniform G)))
      = L (sandwich (centeredElt (lam0.addOrbit hs1 hα) t) x θ) := by
  set a := centeredElt (lam0.addOrbit hs1 hα) t with ha
  have hpos : IsPos a := centeredElt_isPos _ _
  have hsa : IsSelfAdjoint (L a) := isSelfAdjoint_L_centeredElt _ _
  have hLa : reflHeatMat lam0 s t α * (1 - L (uniform G)) = L a := by
    rw [reflHeatMat_eq lam0 hs1 hα, ← L_centeredElt_eq_mul]
  have hPa : L (uniform G) * L a = 0 := L_uniform_mul_L_centeredElt _ _
  have haP : L a * L (uniform G) = 0 := L_centeredElt_mul_L_uniform _ _
  rw [L_sandwich a hpos x hθ0 hθ1, sandwichMat]
  rcases eq_or_lt_of_le hθ0 with hθe | hθp
  · -- `θ = 0`: the first factor is `1 - P` where the sandwich has `1`.
    rw [← hθe]
    simp only [zero_mul, sub_zero, one_mul, reflHeatMat_zero, mpow_zero hsa,
      mpow_one hsa]
    rw [hLa, sub_mul, one_mul, sub_mul, L_uniform_mul_L_single, hPa, sub_zero]
  · rcases eq_or_lt_of_le hθ1 with hθe | hθp'
    · -- `θ = 1`: the second factor is `1 - P` where the sandwich has `1`.
      rw [hθe]
      simp only [sub_self, zero_mul, one_mul, mul_one, reflHeatMat_zero,
        mpow_zero hsa, mpow_one hsa]
      rw [hLa, mul_sub, mul_one, mul_assoc (L a) _ (L (uniform G)),
        L_single_mul_L_uniform, haP, sub_zero]
    · -- `0 < θ < 1`: each factor is separately a fractional power.
      rw [reflHeatMat_mul_compl_eq_powElt lam0 hs1 hα t hθp,
        reflHeatMat_mul_compl_eq_powElt lam0 hs1 hα t
          (show (0 : ℝ) < 1 - θ by linarith),
        L_powElt a hpos hθ0, L_powElt a hpos (show (0 : ℝ) ≤ 1 - θ by linarith)]

/-! ### The power sum as a total function of the orbit rate -/

/-- The centred coefficient, as a total function of the orbit rate. -/
noncomputable def reflCentCo (lam0 : RateFn G) (s : G) (t α : ℝ) (g : G) : ℝ :=
  ((reflHeatMat lam0 s t α * (1 - L (uniform G))) g 1).re

set_option linter.unusedDecidableInType false in
theorem reflCentCo_eq (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ} (hα : 0 ≤ α)
    (t : ℝ) (g : G) :
    reflCentCo lam0 s t α g = co (centeredElt (lam0.addOrbit hs1 hα) t) g := by
  rw [reflCentCo, reflHeatMat_eq lam0 hs1 hα, ← L_centeredElt_eq_mul, L_apply]
  simp

/-- The centred power sum, as a total function of the orbit rate. -/
noncomputable def reflPhi (lam0 : RateFn G) (s : G) (t : ℝ) (m : ℕ) (α : ℝ) : ℝ :=
  ∑ g : G, reflCentCo lam0 s t α g ^ (2 * m)

set_option linter.unusedDecidableInType false in
theorem reflPhi_eq (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ} (hα : 0 ≤ α)
    (t : ℝ) (m : ℕ) :
    reflPhi lam0 s t m α = Phi (lam0.addOrbit hs1 hα) t m := by
  rw [Phi_eq_sum_real, reflPhi]
  exact Finset.sum_congr rfl fun g _ => by
    rw [reflCentCo_eq lam0 hs1 hα, co_centeredElt]

omit [Group G] in
/-- Reading one real entry off a matrix, as a continuous `ℝ`-linear map: this is
what lets the entry and the real part pass through the Duhamel integral. -/
noncomputable def entryReCLM (g h : G) : Matrix G G ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (entryCLM g h)

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem entryReCLM_apply (g h : G) (M : Matrix G G ℂ) :
    entryReCLM g h M = (M g h).re := rfl

/-! ### Differentiating the power sum -/

/-- The whole-orbit Duhamel integrand, as one matrix-valued function of `θ`. -/
noncomputable def orbitIntegrand (lam0 : RateFn G) (s : G) (t α θ : ℝ) :
    Matrix G G ℂ :=
  ∑ x ∈ invOrbit s, duhamelIntegrand lam0 s x t α θ

theorem continuous_orbitIntegrand (lam0 : RateFn G) (s : G) (t α : ℝ) :
    Continuous (orbitIntegrand lam0 s t α) :=
  continuous_finsetSum _ fun x _ => continuous_duhamelIntegrand lam0 s x t α

theorem hasDerivAt_reflCentCo (lam0 : RateFn G) (s : G) (t α : ℝ) (g : G) :
    HasDerivAt (fun a : ℝ => reflCentCo lam0 s t a g)
      (((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re) α :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt α
    ((entryCLM g 1).hasFDerivAt.comp_hasDerivAt α
      (hasDerivAt_reflCentered_integral lam0 s t α))

theorem hasDerivAt_reflPhi (lam0 : RateFn G) (s : G) (t α : ℝ) (m : ℕ) :
    HasDerivAt (fun a : ℝ => reflPhi lam0 s t m a)
      (∑ g : G, ((2 * m : ℕ) : ℝ) * reflCentCo lam0 s t α g ^ (2 * m - 1)
        * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re) α := by
  have h : ∀ g ∈ (Finset.univ : Finset G),
      HasDerivAt (fun a : ℝ => reflCentCo lam0 s t a g ^ (2 * m))
        (((2 * m : ℕ) : ℝ) * reflCentCo lam0 s t α g ^ (2 * m - 1)
          * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re) α :=
    fun g _ => (hasDerivAt_reflCentCo lam0 s t α g).pow (2 * m)
  have hsum := HasDerivAt.sum h
  have hfun : (∑ g : G, fun a : ℝ => reflCentCo lam0 s t a g ^ (2 * m))
      = fun a : ℝ => reflPhi lam0 s t m a := by
    funext a; simp [reflPhi, Finset.sum_apply]
  rwa [hfun] at hsum

/-! ### The sign of the derivative -/

set_option linter.unusedDecidableInType false in
/-- **The derivative is nonpositive**, given the pointwise reflection inequality
at every element of the orbit.

The hypothesis `key` is the reflection inequality; it is taken as an argument so
that this — the integral bookkeeping — stays free of any normal form. It is
needed at *every*
`x ∈ O(s)` simultaneously, which for `z ≠ 0` means at two genuinely different
group elements: no relabelling of the group can send both to one distinguished
element. `Lyons.reflHeatMat_sandwich` is what makes `key` applicable on the
*closed* interval, so no almost-everywhere argument is needed. -/
theorem sum_reflCentCo_pow_mul_deriv_nonpos (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1)
    {α : ℝ} (hα : 0 ≤ α) {t : ℝ} (ht : 0 ≤ t) (p : ℕ)
    (key : ∀ x ∈ invOrbit s, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∑ g : G, co (centeredElt (lam0.addOrbit hs1 hα) t) g ^ (2 * p + 1)
          * co (sandwich (centeredElt (lam0.addOrbit hs1 hα) t) x θ) g
        ≤ ∑ g : G, co (centeredElt (lam0.addOrbit hs1 hα) t) g ^ (2 * p + 2)) :
    ∑ g : G, reflCentCo lam0 s t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re ≤ 0 := by
  set a := centeredElt (lam0.addOrbit hs1 hα) t with ha
  set F := orbitIntegrand lam0 s t α with hFdef
  have hFc : Continuous F := continuous_orbitIntegrand lam0 s t α
  have hFre : ∀ g : G, Continuous fun θ : ℝ => (F θ g 1).re := fun g =>
    (entryReCLM g (1 : G)).continuous.comp hFc
  -- the integrand's real entries, on the closed interval
  have hval : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ g : G,
      (F θ g 1).re = ∑ x ∈ invOrbit s, (co (sandwich a x θ) g - co a g) := by
    intro θ hθ0 hθ1 g
    have h2 : reflHeatMat lam0 s t α * (1 - L (uniform G)) = L a := by
      rw [ha, reflHeatMat_eq lam0 hs1 hα, ← L_centeredElt_eq_mul]
    rw [hFdef, orbitIntegrand, Matrix.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [duhamelIntegrand, reflHeatMat_sandwich lam0 hs1 hα x t hθ0 hθ1, ← ha, h2]
    simp
  -- the entry and the real part pass through the integral
  have hsmul : ∀ g : G, ((t • ∫ θ in (0:ℝ)..1, F θ) g 1).re
      = t * ∫ θ in (0:ℝ)..1, (F θ g 1).re := by
    intro g
    have hc : ((∫ θ in (0:ℝ)..1, F θ) g 1).re = ∫ θ in (0:ℝ)..1, (F θ g 1).re :=
      ((entryReCLM g (1 : G)).intervalIntegral_comp_comm (f := F)
        (μ := MeasureTheory.volume) (hFc.intervalIntegrable 0 1)).symm
    rw [Matrix.smul_apply, Complex.smul_re, hc, smul_eq_mul]
  have hint : ∀ g ∈ (Finset.univ : Finset G), IntervalIntegrable
      (fun θ : ℝ => co a g ^ (2 * p + 1) * (F θ g 1).re) MeasureTheory.volume 0 1 :=
    fun g _ => (continuous_const.mul (hFre g)).intervalIntegrable 0 1
  have hstep : ∑ g : G, reflCentCo lam0 s t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, F θ) g 1).re
      = t * ∫ θ in (0:ℝ)..1, ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re := by
    rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hsmul g, reflCentCo_eq lam0 hs1 hα, ← ha,
      intervalIntegral.integral_const_mul]
    ring
  -- the bracket is nonpositive for every `θ` in the closed interval
  have hbig : Continuous fun θ : ℝ => ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re :=
    continuous_finsetSum _ fun g _ => continuous_const.mul (hFre g)
  have hptwise : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re) ≤ (fun _ : ℝ => (0 : ℝ)) θ := by
    intro θ hθ
    -- exchange the sum over `G` with the sum over the orbit
    have hbracket : ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re
        = ∑ x ∈ invOrbit s,
            ((∑ g : G, co a g ^ (2 * p + 1) * co (sandwich a x θ) g)
              - ∑ g : G, co a g ^ (2 * p + 2)) := by
      rw [Finset.sum_congr rfl fun g _ => by
            rw [hval θ hθ.1 hθ.2 g, Finset.mul_sum],
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [mul_sub, show co a g ^ (2 * p + 1) * co a g = co a g ^ (2 * p + 2) by ring]
    rw [hbracket]
    refine Finset.sum_nonpos fun x hx => ?_
    have := key x hx θ hθ.1 hθ.2
    linarith
  have hle : (∫ θ in (0:ℝ)..1, ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re) ≤ 0 := by
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      zero_le_one (hbig.intervalIntegrable 0 1)
      ((continuous_const (y := (0:ℝ))).intervalIntegrable (0:ℝ) 1) hptwise
    simpa using hmono
  rw [hstep]
  exact mul_nonpos_of_nonneg_of_nonpos ht hle

/-! ### The step -/

set_option linter.unusedDecidableInType false in
/-- **The power sum is antitone in the orbit rate**, given the reflection
inequality at every element of the orbit and at every nonnegative rate.

This is the reflection step, in the total parametrisation. -/
theorem antitoneOn_reflPhi (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1) {t : ℝ}
    (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m)
    (key : ∀ (α : ℝ) (hα : 0 ≤ α), ∀ x ∈ invOrbit s, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ p : ℕ, ∑ g : G, co (centeredElt (lam0.addOrbit hs1 hα) t) g ^ (2 * p + 1)
          * co (sandwich (centeredElt (lam0.addOrbit hs1 hα) t) x θ) g
        ≤ ∑ g : G, co (centeredElt (lam0.addOrbit hs1 hα) t) g ^ (2 * p + 2)) :
    AntitoneOn (fun a : ℝ => reflPhi lam0 s t m a) (Set.Ici 0) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ =>
      (hasDerivAt_reflPhi lam0 s t x (p + 1)).differentiableAt.continuousAt.continuousWithinAt)
    (fun x _ =>
      (hasDerivAt_reflPhi lam0 s t x (p + 1)).differentiableAt.differentiableWithinAt)
    fun α hα => ?_
  rw [interior_Ici] at hα
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hsum := sum_reflCentCo_pow_mul_deriv_nonpos lam0 hs1 hα0 ht p
    (fun x hx θ hθ0 hθ1 => key α hα0 x hx θ hθ0 hθ1 p)
  rw [(hasDerivAt_reflPhi lam0 s t α (p + 1)).deriv,
    show 2 * (p + 1) - 1 = 2 * p + 1 from by omega,
    show 2 * (p + 1) = 2 * p + 2 from by omega]
  have hfactor : ∑ g : G, ((2 * p + 2 : ℕ) : ℝ)
        * reflCentCo lam0 s t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re
      = ((2 * p + 2 : ℕ) : ℝ) * ∑ g : G,
        reflCentCo lam0 s t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum

omit [Fintype G] in
set_option linter.unusedDecidableInType false in
/-- Adding `0` on an orbit changes nothing. -/
theorem RateFn.addOrbit_zero (lam : RateFn G) {s : G} (hs1 : s ≠ 1) :
    lam.addOrbit hs1 (le_refl (0 : ℝ)) = lam :=
  DFunLike.ext _ _ fun g => by
    rw [RateFn.addOrbit_apply]
    split <;> simp

set_option linter.unusedDecidableInType false in
/-- **Raising the rate on one inverse orbit does not increase the power sum**,
given the reflection inequality at every element of the orbit.

This is the reflection step in the form its consumer wants: the two endpoints of
the rate interval `[α_0, α_1]` are `λ` itself and `λ ⊕_s c`, because
`RateFn.addOrbit` *adds* rather than overwrites. -/
theorem Phi_addOrbit_le_of_key (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m)
    (key : ∀ (α : ℝ) (hα : 0 ≤ α), ∀ x ∈ invOrbit s, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ p : ℕ, ∑ g : G, co (centeredElt (lam.addOrbit hs1 hα) t) g ^ (2 * p + 1)
          * co (sandwich (centeredElt (lam.addOrbit hs1 hα) t) x θ) g
        ≤ ∑ g : G, co (centeredElt (lam.addOrbit hs1 hα) t) g ^ (2 * p + 2)) :
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m := by
  have h : reflPhi lam s t m c ≤ reflPhi lam s t m 0 :=
    antitoneOn_reflPhi lam hs1 ht hm key (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      (Set.mem_Ici.mpr hc) hc
  rw [reflPhi_eq lam hs1 hc t m, reflPhi_eq lam hs1 (le_refl (0 : ℝ)) t m,
    RateFn.addOrbit_zero lam hs1] at h
  exact h

end Lyons
