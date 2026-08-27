/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Duhamel
import Lyons.Walk.CenteredRpow

/-!
# Differentiating the centred element in the rate on one inverse orbit

The analytic core of the reflection half of the main theorem. Everything here is
about a general finite group and a general inverse orbit; the inversion-extension
specifics enter only downstream.

## Why the whole orbit, and not one element

An element outside the abelian part of `G_{A,z}` is an involution only when
`z = 0`, so in general its inverse orbit `O(s) = {s, s⁻¹}` has **two** elements
and a symmetric rate function cannot be moved at one of them alone. That is why
the increment here is the orbit element
`ζ_s = ∑_{s' ∈ O(s)} (1 - s')` rather than `1 - b`, and why the derivative
carries an orbit sum `∑_{s' ∈ O} S_{a,θ,s'} - |O| a_α`.

The whole Duhamel computation is linear in the perturbation direction, so it is
done once at a single group element (`Lyons.reflCentered_deriv_value_at`, whose
perturbation element `x` is *independent* of the element `s` indexing the
generator) and then summed over the orbit
(`Lyons.reflCentered_deriv_value_orbit`).

## Why the rate family is re-indexed

`RateFn.addOrbit` takes `0 ≤ α` as a *proof argument*, so `α ↦ λ ⊕_s α` is not a
function of `α` alone and cannot be differentiated as written. The fix is to
observe `Δ_α = Δ_0 + α ζ_s`, whose right side is total in `α`.
So `Lyons.reflLap` is taken as the primitive object,
`Lyons.reflLap_eq_laplacian_addOrbit` identifies it with the rate-family Laplacian
wherever `α ≥ 0`, and the differentiation happens on the total family.

## From the derivative to the sandwich form

`Lyons.hasDerivAt_reflCentered` is the derivative of `L(a_α)` in the orbit rate,
as a Duhamel integral. The algebraic steps that follow it are:

* `Lyons.reflLap_mul_uniform` — the generator annihilates `π_G`, on both sides;
* `Lyons.exp_reflLap_mul_uniform` — hence the semigroup fixes `P`;
* `Lyons.insert_compl_uniform` — inserting `1 - P` to the *left* of `L_x` is free;
* `Lyons.duhamel_integrand_split_at` — the integrand is a constant minus the
  sandwich part, the constant coming from `e^{-sA}e^{(s-t)A} = e^{-tA}`.

The integral calculus is then four steps: `integral_sub` and `integral_const` to
peel off the constant part, `Lyons.integral_mul_const_matrix` to move `1 - P`
inside the integral, the change of variables `s = θt` via
`intervalIntegral.smul_integral_comp_mul_right`, and
`Lyons.powElt_centeredElt` to name `e^{-θtA}(1 - P)` as `L(a_α^θ)`.

## The shape of the statement

`Lyons.hasDerivAt_reflCentered_integral`'s integrand is written with `reflHeatMat`
at the *scaled times* `θt` and `(1-θ)t` rather than as a sandwich
`x_{a_α,θ,s'}`. That is deliberate: written this way it holds for **every** `θ`,
whereas the sandwich form fails at `θ = 0` and `θ = 1` (there `a_α^0 = 1`, not
`1 - P`), which would force an almost-everywhere argument into the statement of the
derivative rather than into its consumer.
`Lyons.reflHeatMat_mul_compl_eq_powElt` supplies the identification for `θ > 0`, so
the sandwich shape is one rewrite away wherever it is wanted.

## Main results

* `Lyons.reflLap` : `Δ_0 + α ζ_s`, total in `α`.
* `Lyons.hasDerivAt_reflHeatMat` : Duhamel, specialised to the orbit rate.
* `Lyons.hasDerivAt_reflCentered` : the same, centred.
* `Lyons.insert_compl_uniform`, `Lyons.duhamel_integrand_split_at` : the algebra of
  the integrand.
* `Lyons.duhamelIntegrand` : the integrand, at one element of the orbit.
* `Lyons.hasDerivAt_reflCentered_integral` : the derivative as an integral over
  `[0, 1]`.
* `Lyons.reflHeatMat_mul_compl_eq_powElt` : the integrand's factors are fractional
  powers of `a_α`.
-/

open Matrix
open scoped Norms.Operator

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

set_option linter.unusedFintypeInType false in
theorem L_orbitElt (s : G) :
    L (orbitElt s) = ∑ x ∈ invOrbit s, (1 - L (MonoidAlgebra.single x (1 : ℝ))) := by
  rw [orbitElt, ← Lalg_apply, map_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Lalg_apply, L_sub, L_one]

/-- The Laplacian of the orbit rate family, as a total function of the rate. -/
noncomputable def reflLap (lam0 : RateFn G) (s : G) (α : ℝ) : MonoidAlgebra ℝ G :=
  laplacian lam0 + α • orbitElt s

theorem L_reflLap (lam0 : RateFn G) (s : G) (α : ℝ) :
    L (reflLap lam0 s α) = L (laplacian lam0) + α • L (orbitElt s) := by
  rw [reflLap, L_add, L_smul]

set_option linter.unusedDecidableInType false in
/-- It agrees with the Laplacian of the orbit increment for a nonnegative rate.

The whole apparatus is built on `RateFn.addOrbit` rather than on
`RateFn.setOrb` because `Lyons.laplacian_addOrbit` already gives the shape
`Δ_0 + α ζ_s` for *any* base rate, with no side condition; the two families agree
by `Lyons.RateFn.setOrb_eq_addOrbit`, which is applied once, at the top. -/
theorem reflLap_eq_laplacian_addOrbit (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1)
    {α : ℝ} (hα : 0 ≤ α) :
    reflLap lam0 s α = laplacian (lam0.addOrbit hs1 hα) :=
  (laplacian_addOrbit lam0 hs1 hα).symm

/-- The heat matrix of the orbit rate family, as a total function of the rate. -/
noncomputable def reflHeatMat (lam0 : RateFn G) (s : G) (t α : ℝ) : Matrix G G ℂ :=
  NormedSpace.exp ((-t) • L (reflLap lam0 s α))

set_option linter.unusedDecidableInType false in
theorem reflHeatMat_eq (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) (t : ℝ) :
    reflHeatMat lam0 s t α = heatMat (lam0.addOrbit hs1 hα) t := by
  rw [reflHeatMat, reflLap_eq_laplacian_addOrbit lam0 hs1 hα, heatMat]
  congr 1
  ext g h
  simp [Complex.real_smul]

/-- **Duhamel, specialised to the orbit rate.** -/
theorem hasDerivAt_reflHeatMat (lam0 : RateFn G) (s : G) (t α : ℝ) :
    HasDerivAt (fun a : ℝ => reflHeatMat lam0 s t a)
      (-∫ σ in (0:ℝ)..t, NormedSpace.exp ((-σ) • L (reflLap lam0 s α)) * L (orbitElt s)
          * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))) α := by
  simp only [reflHeatMat, L_reflLap]
  exact duhamel_deriv _ _ t α

/-- **The derivative of the centred element in the orbit rate.** -/
theorem hasDerivAt_reflCentered (lam0 : RateFn G) (s : G) (t α : ℝ) :
    HasDerivAt (fun a : ℝ => reflHeatMat lam0 s t a * (1 - L (uniform G)))
      ((-∫ σ in (0:ℝ)..t, NormedSpace.exp ((-σ) • L (reflLap lam0 s α)) * L (orbitElt s)
          * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))) * (1 - L (uniform G))) α :=
  (hasDerivAt_reflHeatMat lam0 s t α).mul_const _

/-! ### The algebra of the Duhamel integrand -/

theorem sum_co_orbitElt (s : G) : ∑ g : G, co (orbitElt s) g = 0 := by
  classical
  rw [Finset.sum_congr rfl fun g _ ↦ co_orbitElt s g, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
  simp

theorem reflLap_mul_uniform (lam0 : RateFn G) (s : G) (α : ℝ) :
    reflLap lam0 s α * uniform G = 0 := by
  rw [reflLap, add_mul, laplacian_mul_uniform, smul_mul_assoc, uniform_absorb,
    sum_co_orbitElt, zero_smul, smul_zero, add_zero]

theorem uniform_mul_reflLap (lam0 : RateFn G) (s : G) (α : ℝ) :
    uniform G * reflLap lam0 s α = 0 := by
  rw [reflLap, mul_add, uniform_mul_laplacian, mul_smul_comm, uniform_mul_absorb,
    sum_co_orbitElt, zero_smul, smul_zero, add_zero]

theorem exp_reflLap_mul_uniform (lam0 : RateFn G) (s : G) (α u : ℝ) :
    NormedSpace.exp (u • L (reflLap lam0 s α)) * L (uniform G) = L (uniform G) := by
  refine exp_mul_of_mul_eq_zero ?_
  rw [smul_mul_assoc, ← L_mul, reflLap_mul_uniform, L_zero, smul_zero]

theorem uniform_mul_exp_reflLap (lam0 : RateFn G) (s : G) (α u : ℝ) :
    L (uniform G) * NormedSpace.exp (u • L (reflLap lam0 s α)) = L (uniform G) := by
  refine mul_exp_of_mul_eq_zero ?_
  rw [mul_smul_comm, ← L_mul, uniform_mul_reflLap, L_zero, smul_zero]


set_option linter.unusedDecidableInType false in
theorem uniform_mul_single (b : G) :
    uniform G * MonoidAlgebra.single b (1 : ℝ) = uniform G := by
  classical
  rw [uniform_mul_absorb]
  have : ∑ h : G, co (MonoidAlgebra.single b (1:ℝ)) h = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · intro hcon; exact absurd (Finset.mem_univ b) hcon
  rw [this, one_smul]

set_option linter.unusedDecidableInType false in
theorem L_uniform_mul_L_single (b : G) :
    L (uniform G) * L (MonoidAlgebra.single b (1 : ℝ)) = L (uniform G) := by
  rw [← L_mul, uniform_mul_single]

/-- **Inserting `1 - P` to the left of `L_x` is free.**

The generator is indexed by `s`, the inserted group element by `x`; nothing
relates them, which is exactly what lets the orbit sum be taken termwise. -/
theorem insert_compl_uniform (lam0 : RateFn G) (s x : G) (α u v : ℝ) :
    NormedSpace.exp (u • L (reflLap lam0 s α)) * L (MonoidAlgebra.single x (1:ℝ))
        * NormedSpace.exp (v • L (reflLap lam0 s α)) * (1 - L (uniform G))
      = (NormedSpace.exp (u • L (reflLap lam0 s α)) * (1 - L (uniform G)))
        * L (MonoidAlgebra.single x (1:ℝ))
        * (NormedSpace.exp (v • L (reflLap lam0 s α)) * (1 - L (uniform G))) := by
  set X := NormedSpace.exp (u • L (reflLap lam0 s α)) with hX
  set Y := NormedSpace.exp (v • L (reflLap lam0 s α)) with hY
  set P := L (uniform G) with hP
  set Lx := L (MonoidAlgebra.single x (1:ℝ)) with hLx
  have hXQ : X * (1 - P) = X - P := by rw [mul_sub, mul_one, hX, hP,
    exp_reflLap_mul_uniform]
  have hPLx : P * Lx = P := L_uniform_mul_L_single x
  have hPY : P * (Y * (1 - P)) = 0 := by
    rw [← mul_assoc, hP, hY, uniform_mul_exp_reflLap, mul_sub, mul_one, ← hP,
      L_uniform_mul_self, sub_self]
  symm
  calc (X * (1 - P)) * Lx * (Y * (1 - P))
      = (X - P) * Lx * (Y * (1 - P)) := by rw [hXQ]
    _ = X * Lx * (Y * (1 - P)) - P * Lx * (Y * (1 - P)) := by rw [sub_mul, sub_mul]
    _ = X * Lx * (Y * (1 - P)) - P * (Y * (1 - P)) := by rw [hPLx]
    _ = X * Lx * (Y * (1 - P)) := by rw [hPY, sub_zero]
    _ = X * Lx * Y * (1 - P) := by noncomm_ring


/-- The Duhamel integrand, in the direction of a single group element, splits into
a constant part and a sandwich part. -/
theorem duhamel_integrand_split_at (lam0 : RateFn G) (s x : G) (α t σ : ℝ) :
    NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
        * (1 - L (MonoidAlgebra.single x (1:ℝ)))
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))
      = reflHeatMat lam0 s t α
        - NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
          * L (MonoidAlgebra.single x (1:ℝ))
          * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) := by
  have hcomm : Commute ((-σ) • L (reflLap lam0 s α)) ((σ - t) • L (reflLap lam0 s α)) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hsum : (-σ) • L (reflLap lam0 s α) + (σ - t) • L (reflLap lam0 s α)
      = (-t) • L (reflLap lam0 s α) := by
    rw [← add_smul]
    congr 1
    ring
  have hexp : NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
      * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) = reflHeatMat lam0 s t α := by
    rw [reflHeatMat, ← hsum, Matrix.exp_add_of_commute _ _ hcomm]
  rw [mul_sub, sub_mul, mul_one]
  exact sub_left_inj.mpr hexp

/-! ### The integral calculus, and the derivative -/

omit [Group G] in
noncomputable def mulRightCLM (Q : Matrix G G ℂ) : Matrix G G ℂ →L[ℝ] Matrix G G ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X * Q
      map_add' := fun X Y => add_mul X Y Q
      map_smul' := fun r X => smul_mul_assoc r X Q }

omit [Group G] in
set_option linter.unusedDecidableInType false in
theorem integral_mul_const_matrix (Q : Matrix G G ℂ) (f : ℝ → Matrix G G ℂ)
    (hf : Continuous f) (a b : ℝ) :
    (∫ s in a..b, f s) * Q = ∫ s in a..b, (f s * Q) :=
  ((mulRightCLM Q).intervalIntegral_comp_comm (f := f)
    (μ := MeasureTheory.volume) (hf.intervalIntegrable a b)).symm

/-- The exponential of an affinely reparametrised generator is continuous in the
parameter. -/
theorem continuous_reflExp (lam0 : RateFn G) (s : G) (α : ℝ) (c d : ℝ) :
    Continuous fun σ : ℝ => NormedSpace.exp ((c * σ + d) • L (reflLap lam0 s α)) :=
  NormedSpace.exp_continuous.comp (by fun_prop)

/-- The two exponential factors of the Duhamel integrand, as continuous functions
of the integration variable. -/
private theorem continuous_duhamel_factors (lam0 : RateFn G) (s : G) (α t : ℝ) :
    (Continuous fun σ : ℝ => NormedSpace.exp ((-σ) • L (reflLap lam0 s α)))
      ∧ Continuous fun σ : ℝ => NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) := by
  refine ⟨?_, ?_⟩
  · have := continuous_reflExp lam0 s α (-1) 0
    simpa using this
  · have := continuous_reflExp lam0 s α 1 (-t)
    simpa [sub_eq_add_neg] using this

/-- The Duhamel integral, in the direction of a single group element, with the
constant part peeled off. -/
theorem duhamel_integral_split_at (lam0 : RateFn G) (s x : G) (α t : ℝ) :
    (∫ σ in (0:ℝ)..t, NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
        * (1 - L (MonoidAlgebra.single x (1:ℝ)))
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)))
      = t • reflHeatMat lam0 s t α
        - ∫ σ in (0:ℝ)..t, NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
            * L (MonoidAlgebra.single x (1:ℝ))
            * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) := by
  obtain ⟨hX, hY⟩ := continuous_duhamel_factors lam0 s α t
  have hJ : Continuous fun σ : ℝ => NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
      * L (MonoidAlgebra.single x (1:ℝ))
      * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) :=
    (hX.mul continuous_const).mul hY
  rw [intervalIntegral.integral_congr
      (g := fun σ => reflHeatMat lam0 s t α
        - NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
          * L (MonoidAlgebra.single x (1:ℝ))
          * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)))
      (fun σ _ => duhamel_integrand_split_at lam0 s x α t σ),
    intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable 0 t) (hJ.intervalIntegrable 0 t),
    intervalIntegral.integral_const]
  simp

/-- The integrand of `Lyons.hasDerivAt_reflCentered_integral` at one element `x`
of the orbit, named so that the integral can be manipulated.

The subtracted term is `L(a_α)`, so summing over an orbit `O` produces
`∑_{s' ∈ O} S_{a,θ,s'} - |O| a_α`. -/
noncomputable def duhamelIntegrand (lam0 : RateFn G) (s x : G) (t α θ : ℝ) :
    Matrix G G ℂ :=
  (reflHeatMat lam0 s (θ * t) α * (1 - L (uniform G)))
      * L (MonoidAlgebra.single x (1:ℝ))
      * (reflHeatMat lam0 s ((1 - θ) * t) α * (1 - L (uniform G)))
    - reflHeatMat lam0 s t α * (1 - L (uniform G))

theorem continuous_duhamelIntegrand (lam0 : RateFn G) (s x : G) (t α : ℝ) :
    Continuous (duhamelIntegrand lam0 s x t α) := by
  have h1 : Continuous fun θ : ℝ => reflHeatMat lam0 s (θ * t) α :=
    (continuous_reflExp lam0 s α (-t) 0).congr fun θ => by
      rw [reflHeatMat]; congr 2; ring
  have h2 : Continuous fun θ : ℝ => reflHeatMat lam0 s ((1 - θ) * t) α :=
    (continuous_reflExp lam0 s α t (-t)).congr fun θ => by
      rw [reflHeatMat]; congr 2; ring
  exact (((h1.mul continuous_const).mul continuous_const).mul
    (h2.mul continuous_const)).sub continuous_const

/-- **The derivative value in the direction of one group element**, in the shape
`t ∫₀¹ (… − a_α)`. -/
theorem reflCentered_deriv_value_at (lam0 : RateFn G) (s x : G) (α t : ℝ) :
    (-∫ σ in (0:ℝ)..t, NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
        * (1 - L (MonoidAlgebra.single x (1:ℝ)))
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))) * (1 - L (uniform G))
      = t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 s x t α θ := by
  obtain ⟨hX, hY⟩ := continuous_duhamel_factors lam0 s α t
  have hJ : Continuous fun σ : ℝ => NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
      * L (MonoidAlgebra.single x (1:ℝ))
      * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) :=
    (hX.mul continuous_const).mul hY
  -- the sandwich integrand, as a function of σ
  set Q := (1 : Matrix G G ℂ) - L (uniform G) with hQdef
  have hg : ∀ σ : ℝ, (NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
        * L (MonoidAlgebra.single x (1:ℝ))
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))) * Q
      = (NormedSpace.exp ((-σ) • L (reflLap lam0 s α)) * Q)
        * L (MonoidAlgebra.single x (1:ℝ))
        * (NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) * Q) :=
    fun σ => insert_compl_uniform lam0 s x α (-σ) (σ - t)
  rw [duhamel_integral_split_at lam0 s x α t, neg_sub, sub_mul,
    integral_mul_const_matrix Q _ hJ 0 t,
    intervalIntegral.integral_congr (fun σ _ => hg σ), smul_mul_assoc]
  -- change of variables σ = θ t on the sandwich part
  have hcov := intervalIntegral.smul_integral_comp_mul_right (a := (0:ℝ)) (b := (1:ℝ))
    (fun σ : ℝ => (NormedSpace.exp ((-σ) • L (reflLap lam0 s α)) * Q)
      * L (MonoidAlgebra.single x (1:ℝ))
      * (NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) * Q)) t
  simp only [zero_mul, one_mul] at hcov
  rw [← hcov]
  -- reshape the right-hand side: pull the constant out of its integral
  have hggcont : Continuous fun θ : ℝ =>
      (reflHeatMat lam0 s (θ * t) α * Q) * L (MonoidAlgebra.single x (1:ℝ))
        * (reflHeatMat lam0 s ((1 - θ) * t) α * Q) := by
    have h1 : Continuous fun θ : ℝ => reflHeatMat lam0 s (θ * t) α :=
      (continuous_reflExp lam0 s α (-t) 0).congr fun θ => by
        rw [reflHeatMat]; congr 2; ring
    have h2 : Continuous fun θ : ℝ => reflHeatMat lam0 s ((1 - θ) * t) α :=
      (continuous_reflExp lam0 s α t (-t)).congr fun θ => by
        rw [reflHeatMat]; congr 2; ring
    exact ((h1.mul continuous_const).mul continuous_const).mul (h2.mul continuous_const)
  simp only [duhamelIntegrand, ← hQdef]
  rw [intervalIntegral.integral_sub (hggcont.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1), intervalIntegral.integral_const, smul_sub]
  simp only [sub_zero, one_smul]
  congr 1
  congr 1
  refine intervalIntegral.integral_congr fun y _ ↦ ?_
  rw [reflHeatMat, reflHeatMat, show y * t - t = -((1 - y) * t) by ring]

/-- **The derivative value, summed over the inverse orbit.**

This is `t ∫₀¹ (∑_{s' ∈ O} S_{a,θ,s'} − |O| a_α) dθ`: the `|O|` copies of `a_α`
are the subtracted terms of the `|O|` summands. -/
theorem reflCentered_deriv_value_orbit (lam0 : RateFn G) (s : G) (α t : ℝ) :
    (-∫ σ in (0:ℝ)..t, NormedSpace.exp ((-σ) • L (reflLap lam0 s α)) * L (orbitElt s)
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))) * (1 - L (uniform G))
      = t • ∫ θ in (0:ℝ)..1, ∑ x ∈ invOrbit s, duhamelIntegrand lam0 s x t α θ := by
  obtain ⟨hX, hY⟩ := continuous_duhamel_factors lam0 s α t
  have hterm : ∀ x : G, Continuous fun σ : ℝ =>
      NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
        * (1 - L (MonoidAlgebra.single x (1:ℝ)))
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) :=
    fun x => (hX.mul continuous_const).mul hY
  -- expand the orbit element inside the integral
  have hsplit : ∀ σ : ℝ, NormedSpace.exp ((-σ) • L (reflLap lam0 s α)) * L (orbitElt s)
        * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α))
      = ∑ x ∈ invOrbit s, NormedSpace.exp ((-σ) • L (reflLap lam0 s α))
          * (1 - L (MonoidAlgebra.single x (1:ℝ)))
          * NormedSpace.exp ((σ - t) • L (reflLap lam0 s α)) := by
    intro σ
    rw [L_orbitElt, Finset.mul_sum, Finset.sum_mul]
  rw [intervalIntegral.integral_congr (fun σ _ => hsplit σ),
    intervalIntegral.integral_finsetSum
      (fun x _ => (hterm x).intervalIntegrable 0 t),
    ← Finset.sum_neg_distrib, Finset.sum_mul,
    Finset.sum_congr rfl fun x _ => reflCentered_deriv_value_at lam0 s x α t,
    ← Finset.smul_sum,
    ← intervalIntegral.integral_finsetSum
      (fun x _ => (continuous_duhamelIntegrand lam0 s x t α).intervalIntegrable 0 1)]

/-- **The derivative of the centred element in the rate on one inverse orbit.**

For an involution the orbit is a singleton and the sum has one term. -/
@[lyons_tag "lem_reflection_derivative"]
theorem hasDerivAt_reflCentered_integral (lam0 : RateFn G) (s : G) (t α : ℝ) :
    HasDerivAt (fun a : ℝ => reflHeatMat lam0 s t a * (1 - L (uniform G)))
      (t • ∫ θ in (0:ℝ)..1, ∑ x ∈ invOrbit s, duhamelIntegrand lam0 s x t α θ) α := by
  rw [← reflCentered_deriv_value_orbit lam0 s α t]
  exact hasDerivAt_reflCentered lam0 s t α

set_option linter.unusedDecidableInType false in
/-- Each exponential factor in the integrand is a fractional power of the centred
element — which is what turns the integrand into the sandwich form. -/
theorem reflHeatMat_mul_compl_eq_powElt (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1)
    {α : ℝ} (hα : 0 ≤ α) (t : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    reflHeatMat lam0 s (θ * t) α * (1 - L (uniform G))
      = L (powElt (centeredElt (lam0.addOrbit hs1 hα) t) θ) := by
  rw [reflHeatMat_eq lam0 hs1 hα, ← L_centeredElt_eq_mul, powElt_centeredElt _ _ hθ]

end Lyons
