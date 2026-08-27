/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Contract
import Lyons.Walk.Centered

/-!
# Raising a rate on a central orbit does not increase the power sum

The elementary half of the main theorem, for a general finite group: whenever the
orbit element `ζ_s` happens to be **central**, the two generators commute, the
exponentials factor, and the new centred heat element is the old one convolved
with a probability element — no Duhamel formula and no integral.

Centrality is taken as a hypothesis here; its instance is the abelian part of an
inversion extension (`Lyons.orbitElt_central_rot`), and nothing about the group
is needed for the argument itself.

## The mechanism

Raising the rate on `O(s)` adds `c ζ_s` to the Laplacian
(`Lyons.laplacian_addOrbit`). If `ζ_s` is central the added generator commutes
with the original, so the exponentials factor and

`h_t^{λ'} = h_t^ν h_t^λ`,  `ν` the rate function that is `c` on `O(s)` and `0`
elsewhere.

Absorption (`h_t^ν π_G = π_G`) turns that into a statement about the *centred*
elements, `a_t^{λ'} = h_t^ν a_t^λ`, and `h_t^ν` is a probability element — its
coefficients are nonnegative by `Lyons.heatCoeffReal_nonneg` and sum to one by
`Lyons.sum_heatCoeffReal`. The contraction `Lyons.sum_pow_conv_le` finishes it.

## Main results

* `Lyons.instZeroRateFn` : the zero rate function.
* `Lyons.Phi_eq_sum_co` : `Phi` in terms of the centred element's coefficients.
* `Lyons.Phi_addOrbit_le_of_central` : the central-orbit step.
-/

open Finset

namespace Lyons

/-! ### The zero rate function -/

section Zero

variable {G : Type*} [Group G]

/-- The zero rate function: no jumps at all. -/
instance instZeroRateFn : Zero (RateFn G) where
  zero :=
    { toFun := 0
      nonneg' := fun _ => le_refl 0
      symm' := fun _ => rfl
      atOne := rfl }

@[simp] theorem RateFn.zero_apply (g : G) : (0 : RateFn G) g = 0 := rfl

variable [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
@[simp] theorem laplacian_zero : laplacian (0 : RateFn G) = 0 := by
  rw [laplacian]
  simp

end Zero

/-! ### Centrality from stability of the orbit under conjugation -/

section Stable

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The sum `∑_{s' ∈ O(s)} s'` of an inverse orbit's members — the part of the
orbit sum `ζ_s = ∑_{s' ∈ O(s)}(1 - s')` that is not a multiple of `1`.
`Lyons.orbitElt` is `ζ_s` itself. -/
noncomputable def invOrbitSum (s : G) : MonoidAlgebra ℝ G :=
  ∑ a ∈ invOrbit s, MonoidAlgebra.single a (1 : ℝ)

omit [Fintype G] in
theorem co_invOrbitSum (s g : G) :
    co (invOrbitSum s) g = if g ∈ invOrbit s then 1 else 0 := by
  classical
  rw [invOrbitSum, co_sum]
  by_cases hg : g ∈ invOrbit s
  · rw [if_pos hg, Finset.sum_eq_single g]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hcon; exact absurd hg hcon
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro b hb
    have hne : g ≠ b := fun hcon => hg (by rw [hcon]; exact hb)
    simp [hne]

omit [Fintype G] in
/-- The orbit element is a multiple of `1` minus the orbit sum. -/
theorem orbitElt_eq (s : G) :
    orbitElt s = (invOrbit s).card • (1 : MonoidAlgebra ℝ G) - invOrbitSum s := by
  rw [orbitElt, invOrbitSum, Finset.sum_sub_distrib, Finset.sum_const]

set_option linter.unusedFintypeInType false in
/-- **An inverse orbit stable under conjugation has a central orbit sum.**

A sum over a conjugation-stable set is conjugation-invariant, and that is exactly
what commuting with every group element — hence, by linearity, with every element
of `ℝ[G]` — amounts to. -/
theorem invOrbitSum_central_of_conj_stable {s : G}
    (hstable : ∀ a ∈ invOrbit s, ∀ g : G, g * a * g⁻¹ ∈ invOrbit s)
    (y : MonoidAlgebra ℝ G) : invOrbitSum s * y = y * invOrbitSum s := by
  classical
  refine co_injective fun g ↦ ?_
  rw [co_mul', co_mul]
  have hL : ∀ u : G, co (invOrbitSum s) u * co y (u⁻¹ * g)
      = if u ∈ invOrbit s then co y (u⁻¹ * g) else 0 := by
    intro u; rw [co_invOrbitSum]; by_cases h : u ∈ invOrbit s <;> simp [h]
  have hR : ∀ h' : G, co y (g * h'⁻¹) * co (invOrbitSum s) h'
      = if h' ∈ invOrbit s then co y (g * h'⁻¹) else 0 := by
    intro h'; rw [co_invOrbitSum]; by_cases h : h' ∈ invOrbit s <;> simp [h]
  rw [Finset.sum_congr rfl fun u _ ↦ hL u, Finset.sum_congr rfl fun h' _ ↦ hR h',
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_nbij' (fun u => g⁻¹ * u * g) (fun h' => g * h' * g⁻¹)
    (fun a ha => by simpa using hstable a ha g⁻¹)
    (fun a ha => hstable a ha g)
    (fun a _ => by group) (fun a _ => by group) (fun a _ => ?_)
  congr 1
  group

set_option linter.unusedFintypeInType false in
/-- **An inverse orbit stable under conjugation has a central orbit element.** -/
theorem orbitElt_central_of_conj_stable {s : G}
    (hstable : ∀ a ∈ invOrbit s, ∀ g : G, g * a * g⁻¹ ∈ invOrbit s)
    (y : MonoidAlgebra ℝ G) : orbitElt s * y = y * orbitElt s := by
  rw [orbitElt_eq, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    invOrbitSum_central_of_conj_stable hstable]

end Stable

/-! ### The central-orbit step -/

section Central

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

set_option linter.unusedDecidableInType false in
/-- The Laplacian of the single-orbit rate function is `c ζ_s`. -/
theorem laplacian_zero_addOrbit {s : G} (hs1 : s ≠ 1) {c : ℝ} (hc : 0 ≤ c) :
    laplacian ((0 : RateFn G).addOrbit hs1 hc) = c • orbitElt s := by
  rw [laplacian_addOrbit, laplacian_zero, zero_add]

set_option linter.unusedDecidableInType false in
/-- `Phi` in terms of the centred element's coefficients. -/
theorem Phi_eq_sum_co (lam : RateFn G) (t : ℝ) (m : ℕ) :
    Phi lam t m = ∑ g : G, (co (centeredElt lam t) g) ^ (2 * m) := by
  rw [Phi_eq_sum_real]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [co_centeredElt]

variable {s : G} (hcentral : ∀ y : MonoidAlgebra ℝ G, orbitElt s * y = y * orbitElt s)

include hcentral

set_option linter.unusedDecidableInType false in
/-- The heat element of a **central** orbit increment factors. -/
theorem heatElt_addOrbit_of_central (lam : RateFn G) (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) (t : ℝ) :
    heatElt (lam.addOrbit hs1 hc) t
      = heatElt ((0 : RateFn G).addOrbit hs1 hc) t * heatElt lam t := by
  refine L_injective ?_
  rw [L_mul, L_heatElt, L_heatElt, L_heatElt, heatMat, heatMat, heatMat]
  have hcomm0 : L (laplacian ((0 : RateFn G).addOrbit hs1 hc)) * L (laplacian lam)
      = L (laplacian lam) * L (laplacian ((0 : RateFn G).addOrbit hs1 hc)) := by
    rw [← L_mul, ← L_mul, laplacian_zero_addOrbit hs1 hc, smul_mul_assoc,
      mul_smul_comm, hcentral]
  have hcomm : Commute (-(t : ℂ) • L (laplacian ((0 : RateFn G).addOrbit hs1 hc)))
      (-(t : ℂ) • L (laplacian lam)) :=
    Commute.smul_left (Commute.smul_right hcomm0 _) _
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← smul_add, ← L_add,
    laplacian_addOrbit, laplacian_zero_addOrbit hs1 hc]
  congr 2
  abel_nf

set_option linter.unusedDecidableInType false in
/-- Centring commutes with the factorisation: absorption removes the extra
`π_G`. -/
theorem centeredElt_addOrbit_of_central (lam : RateFn G) (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) (t : ℝ) :
    centeredElt (lam.addOrbit hs1 hc) t
      = heatElt ((0 : RateFn G).addOrbit hs1 hc) t * centeredElt lam t := by
  rw [centeredElt, centeredElt, heatElt_addOrbit_of_central hcentral lam hs1 hc t,
    mul_sub, heatElt_mul_uniform]

set_option linter.unusedDecidableInType false in
/-- **Raising the rate on a central orbit does not increase the power sum.**

Nothing about the group is used; the centrality of `ζ_s` is supplied by the
caller. -/
theorem Phi_addOrbit_le_of_central (lam : RateFn G) (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m := by
  set nu := (0 : RateFn G).addOrbit hs1 hc with hnu
  have hnonneg : ∀ g : G, 0 ≤ co (heatElt nu t) g := by
    intro g
    rw [co_heatElt]
    exact heatCoeffReal_nonneg nu ht g
  have hone : ∑ g : G, co (heatElt nu t) g = 1 := by
    rw [Finset.sum_congr rfl fun g _ ↦ co_heatElt nu t g]
    exact sum_heatCoeffReal nu t
  rw [Phi_eq_sum_co, Phi_eq_sum_co, centeredElt_addOrbit_of_central hcentral lam hs1 hc t]
  exact sum_pow_conv_le _ _ hnonneg hone m

end Central

end Lyons
