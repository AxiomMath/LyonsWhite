/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.Sandwich
import Lyons.Walk.OrbitStep

/-!
# The step outside the abelian part

Over the inversion extension `G_{A,z}`: raising the common rate on an inverse
orbit outside the abelian part does not increase the centred power sum. This is
the half of `Lyons.rateMonotonic_invExt_even` the whole Duhamel/sandwich
apparatus was built for, and it is where
`Lyons.InvExtBlock.sum_co_pow_mul_sandwich_le` — the reflection inequality, §4's
headline — is finally consumed.

## The two-element orbit

For `z = 0` an outside element `ι d τ` is an involution and its inverse orbit is
the singleton `{ι d τ}`. For `z ≠ 0` it is not: `(ι d τ)⁻¹ = ι (z d) τ`
(`InvExt.inv_refl`), so the orbit is
`{ι d τ, ι (z d) τ}` and has **two** elements. Both are outside the abelian part,
so `Lyons.InvExtBlock.sum_co_pow_mul_sandwich_le` applies at each — at the
parameters `d` and `d + z` — and `Lyons.key_refl` is exactly that pair of
instances, packaged as the `key` hypothesis of `Lyons.antitoneOn_reflPhi`.

That is why the reflection inequality is stated at *every* outside element rather
than reduced to one distinguished element: no relabelling of the group can send
both members of the orbit to a single element, so the two instances are genuinely
needed at once.

## Main results

* `Lyons.exists_refl_of_mem_invOrbit_refl` : every element of the orbit of an
  outside element is itself outside.
* `Lyons.key_refl` : the reflection inequality at every element of the orbit.
* `Lyons.differentiableAt_reflPhi_refl`, `Lyons.deriv_reflPhi_refl_nonpos` : the
  power sum is differentiable in an outside rate, with nonpositive derivative.
* `Lyons.Phi_setOrb_refl_le` : increasing an outside rate does not increase the
  power sum.
* `Lyons.Phi_addOrbit_refl_le` : the same, in orbit-increment form.
-/

open Finset Matrix
open scoped Norms.Operator MatrixOrder ComplexOrder

namespace Lyons

variable {A : Type*} [AddCommGroup A] {z : A}

/-- An outside element is never the identity, so it can index an orbit. -/
theorem refl_ne_one (d : A) : (InvExt.refl d : InvExt A z) ≠ 1 := fun h => by
  rw [InvExt.one_def] at h
  cases h

variable [Fact (z + z = 0)] [DecidableEq A]

/-- **The inverse orbit of an outside element stays outside.** Its two members are
`ι d τ` and `ι (z d) τ`, by `InvExt.inv_refl`. -/
theorem exists_refl_of_mem_invOrbit_refl {d : A} {x : InvExt A z}
    (hx : x ∈ invOrbit (InvExt.refl d : InvExt A z)) :
    ∃ d' : A, x = InvExt.refl d' := by
  rcases mem_invOrbit.mp hx with rfl | rfl
  · exact ⟨d, rfl⟩
  · exact ⟨d + z, InvExt.inv_refl d⟩

variable [Fintype A]

set_option linter.unusedDecidableInType false in
/-- **The reflection inequality at every element of the orbit of `ι d τ`.**

For `z ≠ 0` this is two instances of
`Lyons.InvExtBlock.sum_co_pow_mul_sandwich_le`, at `d` and at `d + z`, and both
are needed: the derivative of the power sum contains one sandwich per orbit
member. -/
theorem key_refl (lam : RateFn (InvExt A z)) (d : A) (t : ℝ) :
    ∀ (α : ℝ) (hα : 0 ≤ α), ∀ x ∈ invOrbit (InvExt.refl d : InvExt A z),
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ p : ℕ,
        ∑ g : InvExt A z,
            co (centeredElt (lam.addOrbit (refl_ne_one d) hα) t) g ^ (2 * p + 1)
            * co (sandwich (centeredElt (lam.addOrbit (refl_ne_one d) hα) t) x θ) g
          ≤ ∑ g : InvExt A z,
              co (centeredElt (lam.addOrbit (refl_ne_one d) hα) t) g ^ (2 * p + 2) := by
  intro α hα x hx θ hθ0 hθ1 p
  obtain ⟨d', rfl⟩ := exists_refl_of_mem_invOrbit_refl hx
  exact InvExtBlock.sum_co_pow_mul_sandwich_le d' _ (centeredElt_isPos _ _) hθ0 hθ1 p

set_option linter.unusedDecidableInType false in
/-- **The power sum is differentiable in an outside rate.**

Stated on `Lyons.reflPhi`, the total reparametrisation of
`α ↦ Φ_m(λ[d ↦ α], t)`: the family as the source writes it carries `α ≥ 0` as a
hypothesis, so the map it describes is not a function of `α` and cannot be
differentiated as written. `Lyons.reflPhi_eq` and
`Lyons.RateFn.setOrb_eq_addOrbit` identify the two wherever `α ≥ 0`. -/
@[lyons_tag "lem_Phi_deriv_nonpos"]
theorem differentiableAt_reflPhi_refl (lam : RateFn (InvExt A z)) (d : A) (t α : ℝ)
    (m : ℕ) :
    DifferentiableAt ℝ
      (fun a : ℝ => reflPhi lam (InvExt.refl d) t m a) α :=
  (hasDerivAt_reflPhi lam (InvExt.refl d) t α m).differentiableAt

set_option linter.unusedDecidableInType false in
/-- **The derivative of the power sum in an outside rate is nonpositive.**

This is where `Lyons.InvExtBlock.sum_co_pow_mul_sandwich_le` — the reflection
inequality, the headline of §4 — is finally consumed, at *both* members of the
inverse orbit at once. -/
@[lyons_tag "lem_Phi_deriv_nonpos"]
theorem deriv_reflPhi_refl_nonpos (lam : RateFn (InvExt A z)) (d : A) {α : ℝ}
    (hα : 0 ≤ α) {t : ℝ} (ht : 0 ≤ t) (p : ℕ) :
    deriv (fun a : ℝ => reflPhi lam (InvExt.refl d) t (p + 1) a) α ≤ 0 := by
  have hsum := sum_reflCentCo_pow_mul_deriv_nonpos lam (refl_ne_one d) hα ht p
    (fun x hx θ hθ0 hθ1 => key_refl lam d t α hα x hx θ hθ0 hθ1 p)
  rw [(hasDerivAt_reflPhi lam (InvExt.refl d) t α (p + 1)).deriv,
    show 2 * (p + 1) - 1 = 2 * p + 1 from by omega,
    show 2 * (p + 1) = 2 * p + 2 from by omega]
  have hfactor : ∑ g : InvExt A z, ((2 * p + 2 : ℕ) : ℝ)
        * reflCentCo lam (InvExt.refl d) t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1,
            orbitIntegrand lam (InvExt.refl d) t α θ) g 1).re
      = ((2 * p + 2 : ℕ) : ℝ) * ∑ g : InvExt A z,
        reflCentCo lam (InvExt.refl d) t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1,
            orbitIntegrand lam (InvExt.refl d) t α θ) g 1).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum

set_option linter.unusedDecidableInType false in
/-- **Increasing an outside rate does not increase the power sum**, in the
source's own `λ[d ↦ α]` parametrisation. -/
@[lyons_tag "lem_reflection_step"]
theorem Phi_setOrb_refl_le (lam : RateFn (InvExt A z)) (d : A) {t : ℝ} (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) {α₀ α₁ : ℝ} (h₀ : 0 ≤ α₀) (h₀₁ : α₀ ≤ α₁) :
    Phi (lam.setOrb (refl_ne_one d) (h₀.trans h₀₁)) t m
      ≤ Phi (lam.setOrb (refl_ne_one d) h₀) t m := by
  set lam0 := lam.setOrb (refl_ne_one d) (le_refl (0 : ℝ)) with hlam0
  have h : reflPhi lam0 (InvExt.refl d) t m α₁ ≤ reflPhi lam0 (InvExt.refl d) t m α₀ :=
    antitoneOn_reflPhi lam0 (refl_ne_one d) ht hm (key_refl lam0 d t)
      (Set.mem_Ici.mpr h₀) (Set.mem_Ici.mpr (h₀.trans h₀₁)) h₀₁
  rw [reflPhi_eq lam0 (refl_ne_one d) (h₀.trans h₀₁) t m,
    reflPhi_eq lam0 (refl_ne_one d) h₀ t m, hlam0,
    ← RateFn.setOrb_eq_addOrbit lam (refl_ne_one d) (h₀.trans h₀₁),
    ← RateFn.setOrb_eq_addOrbit lam (refl_ne_one d) h₀] at h
  exact h

set_option linter.unusedDecidableInType false in
/-- **Raising the rate on an outside inverse orbit does not increase the power
sum**, in the orbit-increment form the induction consumes. -/
theorem Phi_addOrbit_refl_le (lam : RateFn (InvExt A z)) (d : A) {c : ℝ}
    (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    Phi (lam.addOrbit (refl_ne_one d) hc) t m ≤ Phi lam t m :=
  Phi_addOrbit_le_of_key lam (refl_ne_one d) hc ht hm (key_refl lam d t)

end Lyons
