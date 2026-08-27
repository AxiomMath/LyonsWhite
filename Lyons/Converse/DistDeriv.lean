/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Energy
import Lyons.InversionExtension.ReflectionStep

/-!
# Differentiating the `ℓ^p` power sum in an outside rate

For a symmetric rate function `ν`, a real `p ≥ 1` and an outside element `ι d τ`
of the inversion extension `G_{A,1}`, the map

  `β ↦ ∑_{g ∈ G} |(a_t^{ν[d ↦ β]})_g|^p`

is differentiable at `β = α` with derivative
`p · t · E_p(a_t^{ν[d ↦ α]}; ι d τ)`, provided every coefficient of
`a_t^{ν[d ↦ α]}` is nonzero.

This is the mirror image of `Lyons.deriv_reflPhi_refl_nonpos`: the same Duhamel
derivative and the same sandwich integrand, with the even power `y ↦ y^{2m}`
replaced by `y ↦ |y|^p` and the conclusion read as an *energy* rather than as a
sign. Everything analytic is therefore already available from
`Lyons.Walk.OrbitStep`; what is new here is the outer function and the
recognition of the resulting integral as `Lyons.Converse.energy`.

## Main definitions

* `Lyons.Converse.reflDistPow` : the `p`-th power sum of the centred
  coefficients, total in the orbit rate.

## Main results

* `Lyons.invOrbit_eq_singleton` : an involution has a singleton inverse orbit.
* `Lyons.refl_inv_self` : an outside element of `G_{A,0}` is an involution.
* `Lyons.Converse.reflDistPow_setOrb` : the total family agrees with the power
  sum along `ν[d ↦ β]`.
* `Lyons.Converse.hasDerivAt_reflDistPow` : the derivative, for a general
  involution.
* `Lyons.Converse.hasDerivAt_reflDistPow_setOrb_refl` : the derivative at an
  outside element.

## Implementation notes

*Why `z = 1` — the singleton orbit.* `Lyons.hasDerivAt_reflCentered_integral`
produces one Duhamel term per element of the inverse orbit `O(s)`, while
`Lyons.Converse.energy` contains a *single* sandwich. The two match only when the
orbit is a singleton, that is when `s⁻¹ = s`. For an outside element
`ι d τ = InvExt.refl d` of `G_{A,z}` one has `(ι d τ)⁻¹ = ι (z d) τ`
(`InvExt.inv_refl`), so this happens exactly when `z = 0` — the condition `z = 1`
written additively. `Lyons.invOrbit_eq_singleton` is the collapse and
`Lyons.refl_inv_self` is the instance of it used here. For `z ≠ 0` the right-hand
side would instead be a sum of two energies at two different outside elements.

*Why the nonvanishing hypothesis.*
`Lyons.Converse.hasDerivAt_abs_rpow_signedPow` needs `y ≠ 0`, because at `p = 1`
the map `y ↦ |y|` is not differentiable at the origin. The hypothesis is carried
for every `p ≥ 1`, so that there is no case distinction on `p`; the consumer
discharges it from `Lyons.Converse.coeff_testElement_ne_zero` and
`Lyons.Converse.coeff_regTestElement_ne_zero`.

*The family is reparametrised.* `Lyons.RateFn.setOrb` takes `0 ≤ β` as a *proof
argument*, so `β ↦ ν[d ↦ β]` is not a function of `β` and cannot be
differentiated as written. `Lyons.Converse.reflDistPow` is the total version,
built on `Lyons.reflCentCo`, and `Lyons.Converse.reflDistPow_setOrb` identifies
it with the power sum wherever `β ≥ 0`. This is the same device, for the same
reason, as `Lyons.reflPhi`, where `Lyons.differentiableAt_reflPhi_refl` is stated
the same way.

*A general finite group and a general involution.* The analytic content
(`Lyons.Converse.hasDerivAt_reflDistPow`) is stated for an arbitrary finite group
and any `s ≠ 1` with `s⁻¹ = s`; nothing in it looks at the inversion extension.
`Lyons.Converse.hasDerivAt_reflDistPow_setOrb_refl` is its instance at
`s = ι d τ` over `G_{A,0}`, in the `ν[d ↦ β]` parametrisation, and this mirrors
how `Lyons.antitoneOn_reflPhi` supports `Lyons.Phi_setOrb_refl_le`.

*Weak hypotheses on `t` and `α`.* `t` is arbitrary and only `0 ≤ α` is required,
that being what identifies the total family with the power sum at `α`. The
consumer has `α > 0` anyway, from strict positivity of the realising rate.

*`HasDerivAt`, not `DifferentiableAt` plus a `deriv` equation.* That is the shape
`Lyons.exists_gt_of_hasDerivAt_pos` consumes, and it carries the derivative's
value without a second lemma.

*No almost-everywhere argument.* The sandwich is meaningful only on the open
interval, but `Lyons.reflHeatMat_sandwich` shows the Duhamel integrand equals the
sandwich on the *closed* `[0, 1]` — the endpoint discrepancy is a multiple of
`π_G`, which `L a_α` annihilates — so `intervalIntegral.integral_congr` applies
pointwise and no `ae` filter appears.
-/
open Finset Matrix
open scoped Norms.Operator MatrixOrder ComplexOrder

namespace Lyons

/-! ### The inverse orbit of an involution -/

section Involution

variable {G : Type*} [Group G] [DecidableEq G]

/-- **An involution has a singleton inverse orbit**: `O(s) = {s, s⁻¹} = {s}`.

This is the step that collapses the Duhamel orbit sum to the single sandwich of
`Lyons.Converse.energy`. -/
theorem invOrbit_eq_singleton {s : G} (hs : s⁻¹ = s) : invOrbit s = {s} := by
  rw [invOrbit, hs, Finset.pair_eq_singleton]

end Involution

/-- **An outside element of `G_{A,0}` is an involution**:
`(ι d τ)⁻¹ = ι (z d) τ = ι d τ` when `z = 0`.

The hypothesis `z = 0` is `z = 1` written additively, and it is exactly what the
singleton orbit — hence the derivative formula below — needs. -/
theorem refl_inv_self {A : Type*} [AddCommGroup A] {z : A} (hz : z = 0) (d : A) :
    (InvExt.refl d : InvExt A z)⁻¹ = InvExt.refl d := by
  rw [InvExt.inv_refl, hz, add_zero]

namespace Converse

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### The power sum as a total function of the orbit rate -/

/-- The `p`-th power sum of the centred coefficients, as a total function of the
orbit rate: `∑_{g ∈ G} |(a_t)_g|^p`. The exponent is a real number, so the power
is `Real.rpow`.

Total in the rate for the reason spelled out in the module docstring:
`Lyons.RateFn.setOrb` carries `0 ≤ β` as a proof argument, so the family
`β ↦ ν[d ↦ β]` is not a function of `β`. -/
noncomputable def reflDistPow (lam0 : RateFn G) (s : G) (t p α : ℝ) : ℝ :=
  ∑ g : G, |reflCentCo lam0 s t α g| ^ p

set_option linter.unusedDecidableInType false in
/-- The total family is the power sum of the orbit increment, wherever the rate
moved onto the orbit is nonnegative. -/
theorem reflDistPow_eq (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ} (hα : 0 ≤ α)
    (t p : ℝ) :
    reflDistPow lam0 s t p α
      = ∑ g : G, |co (centeredElt (lam0.addOrbit hs1 hα) t) g| ^ p := by
  rw [reflDistPow]
  exact Finset.sum_congr rfl fun g _ => by rw [reflCentCo_eq lam0 hs1 hα]

set_option linter.unusedDecidableInType false in
/-- **The total family is the power sum along `ν[d ↦ β]`.** For `β ≥ 0`,

  `reflDistPow (ν[d ↦ 0]) s t p β = ∑_{g ∈ G} |(a_t^{ν[d ↦ β]})_g|^p`.

The base rate is `ν[d ↦ 0]`, the member of that family at `β = 0`, because
`Lyons.RateFn.addOrbit` adds where `Lyons.RateFn.setOrb` overwrites;
`Lyons.RateFn.setOrb_eq_addOrbit` is what reconciles the two. -/
theorem reflDistPow_setOrb (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {β : ℝ}
    (hβ : 0 ≤ β) (t p : ℝ) :
    reflDistPow (lam.setOrb hs1 (le_refl (0 : ℝ))) s t p β
      = ∑ g : G, |co (centeredElt (lam.setOrb hs1 hβ) t) g| ^ p := by
  rw [reflDistPow_eq _ hs1 hβ, ← RateFn.setOrb_eq_addOrbit lam hs1 hβ]

/-! ### The derivative -/

set_option linter.unusedDecidableInType false in
/-- **The derivative of the `p`-th power sum in the rate on a singleton inverse
orbit.** The analytic content, for an arbitrary finite group and an arbitrary
involution `s ≠ 1`.

Three inputs meet here. `Lyons.hasDerivAt_reflCentCo` differentiates each centred
coefficient in the rate, with a Duhamel integral as its derivative;
`Lyons.reflHeatMat_sandwich` identifies that integrand with the sandwich
`S_{a_α,θ,s}`; and `Lyons.Converse.hasDerivAt_abs_rpow_signedPow` differentiates
`y ↦ |y|^p` at each coefficient, which is where `hne` is spent. The chain rule and
the finite sum rule give the derivative as `∑_g p J_p((a_α)_g) · t ∫₀¹ (…) dθ`,
and exchanging the finite sum with the integral — legitimate by linearity, the
integrands being continuous — turns it into `Lyons.Converse.energy`.

`hsinv` is what makes the orbit a singleton, so that the one Duhamel term per
orbit element becomes the one sandwich of `Lyons.Converse.energy`. -/
theorem hasDerivAt_reflDistPow (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1)
    (hsinv : s⁻¹ = s) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hne : ∀ g : G, co (centeredElt (lam0.addOrbit hs1 hα) t) g ≠ 0) :
    HasDerivAt (fun β : ℝ => reflDistPow lam0 s t p β)
      (p * t * energy p (centeredElt (lam0.addOrbit hs1 hα) t) s) α := by
  set a := centeredElt (lam0.addOrbit hs1 hα) t with ha
  have hFc : Continuous (orbitIntegrand lam0 s t α) :=
    continuous_orbitIntegrand lam0 s t α
  have hFre : ∀ g : G, Continuous fun θ : ℝ => (orbitIntegrand lam0 s t α θ g 1).re :=
    fun g => (entryReCLM g (1 : G)).continuous.comp hFc
  have hco : ∀ g : G, reflCentCo lam0 s t α g = co a g := fun g =>
    reflCentCo_eq lam0 hs1 hα t g
  -- the orbit is a singleton, so the Duhamel integrand is a single sandwich
  have hval : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ g : G,
      (orbitIntegrand lam0 s t α θ g 1).re = co (sandwich a s θ) g - co a g := by
    intro θ hθ g
    have h2 : reflHeatMat lam0 s t α * (1 - L (uniform G)) = L a := by
      rw [ha, reflHeatMat_eq lam0 hs1 hα, ← L_centeredElt_eq_mul]
    rw [orbitIntegrand, invOrbit_eq_singleton hsinv, Finset.sum_singleton,
      duhamelIntegrand, reflHeatMat_sandwich lam0 hs1 hα s t hθ.1 hθ.2, ← ha, h2]
    simp
  -- the entry and the real part pass through the Duhamel integral
  have hsmul : ∀ g : G,
      ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re
        = t * ∫ θ in (0:ℝ)..1, (orbitIntegrand lam0 s t α θ g 1).re := by
    intro g
    have hc : ((∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re
        = ∫ θ in (0:ℝ)..1, (orbitIntegrand lam0 s t α θ g 1).re :=
      ((entryReCLM g (1 : G)).intervalIntegral_comp_comm
        (f := orbitIntegrand lam0 s t α) (μ := MeasureTheory.volume)
        (hFc.intervalIntegrable 0 1)).symm
    rw [Matrix.smul_apply, Complex.smul_re, hc, smul_eq_mul]
  -- the chain rule, coefficient by coefficient
  have hgderiv : ∀ g ∈ (Finset.univ : Finset G),
      HasDerivAt (fun β : ℝ => |reflCentCo lam0 s t β g| ^ p)
        (p * signedPow p (co a g)
          * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re) α := by
    intro g _
    exact (hasDerivAt_abs_rpow_signedPow hp (hne g)).comp_of_eq α
      (hasDerivAt_reflCentCo lam0 s t α g) (hco g).symm
  -- the finite sum rule
  have hsum := HasDerivAt.sum hgderiv
  have hfun : (∑ g : G, fun β : ℝ => |reflCentCo lam0 s t β g| ^ p)
      = fun β : ℝ => reflDistPow lam0 s t p β := by
    funext β; simp [reflDistPow, Finset.sum_apply]
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  -- exchange the finite sum with the integral, and recognise the energy
  have hint : ∀ g ∈ (Finset.univ : Finset G), IntervalIntegrable
      (fun θ : ℝ => signedPow p (co a g) * (orbitIntegrand lam0 s t α θ g 1).re)
      MeasureTheory.volume 0 1 :=
    fun g _ => (continuous_const.mul (hFre g)).intervalIntegrable 0 1
  have hterm : ∀ g : G, p * signedPow p (co a g)
        * ((t • ∫ θ in (0:ℝ)..1, orbitIntegrand lam0 s t α θ) g 1).re
      = p * t * ∫ θ in (0:ℝ)..1,
          signedPow p (co a g) * (orbitIntegrand lam0 s t α θ g 1).re := by
    intro g
    rw [hsmul g, intervalIntegral.integral_const_mul]
    ring
  rw [Finset.sum_congr rfl fun g _ => hterm g, ← Finset.mul_sum,
    ← intervalIntegral.integral_finsetSum hint, energy_def]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le zero_le_one] at hθ
  exact Finset.sum_congr rfl fun g _ => by rw [hval θ hθ g]

set_option linter.unusedDecidableInType false in
/-- **The derivative of the `p`-th power sum in an outside rate.**

The function is `Lyons.Converse.reflDistPow` at the base rate `ν[d ↦ 0]`, which
`Lyons.Converse.reflDistPow_setOrb` identifies with
`β ↦ ∑_{g ∈ G} |(a_t^{ν[d ↦ β]})_g|^p` for every `β ≥ 0`; see the module
docstring for why the reparametrisation is forced.

`hz : z = 0` is `z = 1`, written additively. It enters exactly
once, through `Lyons.refl_inv_self`: it is what makes `ι d τ` an involution,
hence its inverse orbit a singleton, hence the derivative a single energy. -/
@[lyons_tag "lem_dist_p_deriv"]
theorem hasDerivAt_reflDistPow_setOrb_refl {A : Type*} [AddCommGroup A] [Fintype A]
    [DecidableEq A] {z : A} [Fact (z + z = 0)] (hz : z = 0)
    (ν : RateFn (InvExt A z)) (d : A) (t : ℝ) {α : ℝ} (hα : 0 ≤ α) {p : ℝ}
    (hp : 1 ≤ p)
    (hne : ∀ g : InvExt A z,
      co (centeredElt (ν.setOrb (refl_ne_one d) hα) t) g ≠ 0) :
    HasDerivAt
      (fun β : ℝ => reflDistPow (ν.setOrb (refl_ne_one d) (le_refl (0 : ℝ)))
        (InvExt.refl d) t p β)
      (p * t * energy p (centeredElt (ν.setOrb (refl_ne_one d) hα) t)
        (InvExt.refl d)) α := by
  rw [RateFn.setOrb_eq_addOrbit ν (refl_ne_one d) hα] at hne ⊢
  exact hasDerivAt_reflDistPow _ (refl_ne_one d) (refl_inv_self hz d) hα t hp hne

end Converse

end Lyons
