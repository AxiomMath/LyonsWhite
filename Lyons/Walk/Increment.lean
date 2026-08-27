/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Heat

/-!
# Raising the rate on one inverse orbit

The final induction raises rates one inverse orbit at a time. This file builds
the increment, checks it is again a symmetric rate function, and computes the
effect on the Laplacian.

## Implementation notes

`Lyons.RateFn.addOrbit` and `Lyons.RateFn.setOrb` both *return* a `RateFn G`, and
`RateFn G` is by definition the type of symmetric rate functions, so symmetry of
the increment carries no content beyond those definitions.
`Lyons.RateFn.addOrbit_isRate` and `Lyons.RateFn.setOrb_isRate` record it anyway,
by spelling the three defining conditions out.

## Main definitions

* `Lyons.RateFn.addOrbit` : `λ ⊕_s c`.
* `Lyons.orbitElt` : `ζ_s = ∑_{s' ∈ O s} (1 - s')`.

## Main results

* `Lyons.laplacian_addOrbit` : `Δ_{λ ⊕_s c} = Δ_λ + c ζ_s`.
-/

open Finset

namespace Lyons

section Rate

variable {G : Type*} [Group G] [DecidableEq G]

/-- An inverse orbit is closed under inversion, in both directions. -/
@[simp] theorem inv_mem_invOrbit_iff {s g : G} : g⁻¹ ∈ invOrbit s ↔ g ∈ invOrbit s :=
  ⟨fun h => by simpa using inv_mem_invOrbit h, inv_mem_invOrbit⟩

/-- The identity is never in an inverse orbit of a non-identity element. -/
theorem one_notMem_invOrbit {s : G} (hs1 : s ≠ 1) : (1 : G) ∉ invOrbit s := by
  intro h
  rcases mem_invOrbit.mp h with h | h
  · exact hs1 h.symm
  · exact hs1 (by simpa using h.symm)

/-- **Raising the rate on one inverse orbit**, `λ ⊕_s c`. -/
@[lyons_tag "def_orbit_increment"]
noncomputable def RateFn.addOrbit (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) : RateFn G where
  toFun g := if g ∈ invOrbit s then lam g + c else lam g
  nonneg' g := by
    by_cases h : g ∈ invOrbit s
    · simpa [h] using add_nonneg (lam.nonneg g) hc
    · simpa [h] using lam.nonneg g
  symm' g := by
    by_cases h : g ∈ invOrbit s
    · rw [if_pos (inv_mem_invOrbit_iff.mpr h), if_pos h, lam.symm]
    · rw [if_neg (fun hcon => h (inv_mem_invOrbit_iff.mp hcon)), if_neg h, lam.symm]
  atOne := by simp [one_notMem_invOrbit hs1]

@[simp] theorem RateFn.addOrbit_apply (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) (g : G) :
    lam.addOrbit hs1 hc g = if g ∈ invOrbit s then lam g + c else lam g := rfl

/-- **An orbit increment is a symmetric rate function.** The claim is the type of
`Lyons.RateFn.addOrbit`, so this spells the three conditions out. -/
@[lyons_tag "lem_increment_symmetric"]
theorem RateFn.addOrbit_isRate (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) :
    (∀ g : G, 0 ≤ lam.addOrbit hs1 hc g) ∧
      (∀ g : G, lam.addOrbit hs1 hc g⁻¹ = lam.addOrbit hs1 hc g) ∧
        lam.addOrbit hs1 hc 1 = 0 :=
  ⟨fun g => (lam.addOrbit hs1 hc).nonneg g, fun g => (lam.addOrbit hs1 hc).symm g,
    (lam.addOrbit hs1 hc).apply_one⟩

/-- **The outside rate family** `λ[d ↦ α]`: the common rate `α` on the whole
inverse orbit of `s`, and `λ` elsewhere.

The rate is set on a whole *orbit* rather than at a single reflection, and that is
forced: an element outside the abelian part of `G_{A,z}` is an involution only
when `z = 0`, so in general its inverse orbit has two elements and a symmetric
rate function cannot be moved at one of them alone. -/
@[lyons_tag "def_refl_family"]
noncomputable def RateFn.setOrb (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) : RateFn G where
  toFun g := if g ∈ invOrbit s then α else lam g
  nonneg' g := by
    by_cases h : g ∈ invOrbit s
    · simpa [h] using hα
    · simpa [h] using lam.nonneg g
  symm' g := by
    by_cases h : g ∈ invOrbit s
    · rw [if_pos (inv_mem_invOrbit_iff.mpr h), if_pos h]
    · rw [if_neg (fun hcon => h (inv_mem_invOrbit_iff.mp hcon)), if_neg h, lam.symm]
  atOne := by simp [one_notMem_invOrbit hs1]

@[simp] theorem RateFn.setOrb_apply (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) (g : G) :
    lam.setOrb hs1 hα g = if g ∈ invOrbit s then α else lam g := rfl

/-- **The outside rate family consists of symmetric rate functions.** The claim is
the type of `Lyons.RateFn.setOrb`, so this spells the three conditions out. -/
@[lyons_tag "lem_refl_family_symmetric"]
theorem RateFn.setOrb_isRate (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) :
    (∀ g : G, 0 ≤ lam.setOrb hs1 hα g) ∧
      (∀ g : G, lam.setOrb hs1 hα g⁻¹ = lam.setOrb hs1 hα g) ∧
        lam.setOrb hs1 hα 1 = 0 :=
  ⟨fun g => (lam.setOrb hs1 hα).nonneg g, fun g => (lam.setOrb hs1 hα).symm g,
    (lam.setOrb hs1 hα).apply_one⟩

/-- The outside rate family is an orbit increment on the family's own base point:
`λ[d ↦ α] = λ[d ↦ 0] ⊕_s α`. This is what lets the whole analytic apparatus be
built on `Lyons.RateFn.addOrbit`, which is total, and only then be restated for
the `setOrb` family. -/
theorem RateFn.setOrb_eq_addOrbit (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) :
    lam.setOrb hs1 hα = (lam.setOrb hs1 (le_refl (0 : ℝ))).addOrbit hs1 hα :=
  DFunLike.ext _ _ fun g => by
    rw [RateFn.addOrbit_apply, RateFn.setOrb_apply, RateFn.setOrb_apply]
    by_cases h : g ∈ invOrbit s
    · rw [if_pos h, if_pos h, if_pos h, zero_add]
    · rw [if_neg h, if_neg h, if_neg h]

end Rate

section Laplacian

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The **orbit sum** `ζ_s = ∑_{s' ∈ O s} (1 - s')`, the increment the Laplacian
picks up. -/
@[lyons_tag "def_orbit_sum"]
noncomputable def orbitElt (s : G) : MonoidAlgebra ℝ G :=
  ∑ s' ∈ invOrbit s, (1 - MonoidAlgebra.single s' (1 : ℝ))

omit [Fintype G] in
theorem co_orbitElt (s g : G) :
    co (orbitElt s) g
      = (invOrbit s).card * (if g = 1 then (1 : ℝ) else 0)
        - (if g ∈ invOrbit s then 1 else 0) := by
  classical
  rw [orbitElt, co_sum]
  have hterm : ∀ s' ∈ invOrbit s, co (1 - MonoidAlgebra.single s' (1 : ℝ)) g
      = (if g = 1 then (1 : ℝ) else 0) - (if g = s' then 1 else 0) := by
    intro s' _
    rw [co_sub, co_one, co_single]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  by_cases hg : g ∈ invOrbit s
  · rw [if_pos hg, Finset.sum_eq_single g]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hcon; exact absurd hg hcon
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro b hb
    exact if_neg fun hcon => hg (by rw [hcon]; exact hb)

/-- The total rate of an increment: `Λ` goes up by `c` times the orbit size. -/
theorem sum_addOrbit (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ} (hc : 0 ≤ c) :
    ∑ g : G, lam.addOrbit hs1 hc g
      = (∑ g : G, lam g) + (invOrbit s).card * c := by
  classical
  have hsplit : ∀ g : G, lam.addOrbit hs1 hc g
      = lam g + (if g ∈ invOrbit s then c else 0) := by
    intro g
    by_cases h : g ∈ invOrbit s <;> simp [h]
  rw [Finset.sum_congr rfl fun g _ ↦ hsplit g, Finset.sum_add_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

set_option linter.unusedDecidableInType false in
/-- **The Laplacian of an orbit increment.** -/
@[lyons_tag "lem_increment_laplacian"]
theorem laplacian_addOrbit (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) :
    laplacian (lam.addOrbit hs1 hc) = laplacian lam + c • orbitElt s := by
  refine co_injective fun g ↦ ?_
  rw [coe_laplacian, co_add, co_smul, coe_laplacian, co_orbitElt,
    sum_addOrbit lam hs1 hc, RateFn.addOrbit_apply]
  by_cases hg1 : g = 1
  · subst hg1
    simp [one_notMem_invOrbit hs1]
    ring
  · by_cases hg : g ∈ invOrbit s
    · simp [hg1, hg]; ring
    · simp [hg1, hg]

end Laplacian

end Lyons
