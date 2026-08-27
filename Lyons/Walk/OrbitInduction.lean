/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Increment

/-!
# Interpolating between ordered rate functions

If raising the rate on *one* inverse orbit never increases the power sum, then
raising every rate never does either.

## The induction

The induction runs on the *size of the disagreement set* `{g | λ g ≠ μ g}` rather
than on an enumeration `λ⁽⁰⁾, …, λ⁽ᴺ⁾` of the inverse orbits: the same argument,
with the enumeration replaced by a measure that visibly decreases. One increment
removes a whole inverse orbit from that set, because both
rate functions are constant on an inverse orbit
(`Lyons.RateFn.apply_of_mem_invOrbit`) so the increment lands exactly on `μ`
there — not merely below it.

## Main results

* `Lyons.disagree` : the disagreement set of two rate functions.
* `Lyons.Phi_le_of_le_of_step` : the induction, from the one-orbit step.
-/

open Finset

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

set_option linter.unusedDecidableInType false in
/-- The disagreement set of two rate functions. -/
noncomputable def disagree (lam mu : RateFn G) : Finset G :=
  open Classical in Finset.univ.filter fun g => lam g ≠ mu g

omit [DecidableEq G] in
set_option linter.unusedDecidableInType false in
theorem mem_disagree {lam mu : RateFn G} {g : G} :
    g ∈ disagree lam mu ↔ lam g ≠ mu g := by
  classical
  simp [disagree]

omit [DecidableEq G] in
set_option linter.unusedDecidableInType false in
theorem eq_of_disagree_eq_empty {lam mu : RateFn G} (h : disagree lam mu = ∅) :
    lam = mu := by
  refine DFunLike.ext _ _ fun g => ?_
  by_contra hg
  exact absurd (mem_disagree.mpr hg) (by rw [h]; exact Finset.notMem_empty g)

/-- The one-orbit step, as a hypothesis: raising the rate on a single inverse
orbit does not increase the power sum. -/
def OneOrbitStep (G : Type*) [Group G] [Fintype G] [DecidableEq G] (t : ℝ)
    (m : ℕ) : Prop :=
  ∀ (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {c : ℝ} (hc : 0 ≤ c),
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m

set_option linter.unusedDecidableInType false in
/-- The induction on the size of the disagreement set. -/
theorem Phi_le_of_le_aux {t : ℝ} {m : ℕ} (step : OneOrbitStep G t m) :
    ∀ N : ℕ, ∀ lam mu : RateFn G, (∀ g, lam g ≤ mu g) →
      (disagree lam mu).card ≤ N → Phi mu t m ≤ Phi lam t m := by
  intro N
  induction N with
  | zero =>
    intro lam mu _ hcard
    rw [eq_of_disagree_eq_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))]
  | succ N ih =>
    intro lam mu hle hcard
    rcases Finset.eq_empty_or_nonempty (disagree lam mu) with hne | ⟨s, hs⟩
    · rw [eq_of_disagree_eq_empty hne]
    have hsne : lam s ≠ mu s := mem_disagree.mp hs
    have hs1 : s ≠ 1 := fun h => hsne (by rw [h, lam.apply_one, mu.apply_one])
    have hc : (0 : ℝ) ≤ mu s - lam s := by have := hle s; linarith
    set lam' : RateFn G := lam.addOrbit hs1 hc with hlam'
    -- on the raised orbit the increment lands exactly on `mu`
    have horb : ∀ g : G, g ∈ invOrbit s → lam' g = mu g := by
      intro g hg
      rw [hlam', RateFn.addOrbit_apply, if_pos hg,
        lam.apply_of_mem_invOrbit hg, mu.apply_of_mem_invOrbit hg]
      ring
    have hoff : ∀ g : G, g ∉ invOrbit s → lam' g = lam g := by
      intro g hg
      rw [hlam', RateFn.addOrbit_apply, if_neg hg]
    have hle' : ∀ g, lam' g ≤ mu g := by
      intro g
      by_cases hg : g ∈ invOrbit s
      · exact le_of_eq (horb g hg)
      · rw [hoff g hg]; exact hle g
    -- the disagreement set has lost the whole orbit of `s`, in particular `s`
    have hsub : disagree lam' mu ⊆ (disagree lam mu).erase s := by
      intro g hg
      have hg' : lam' g ≠ mu g := mem_disagree.mp hg
      have hgo : g ∉ invOrbit s := fun h => hg' (horb g h)
      refine Finset.mem_erase.mpr ⟨fun hcon =>
        hgo (hcon ▸ mem_invOrbit.mpr (Or.inl rfl)), ?_⟩
      exact mem_disagree.mpr (by rw [← hoff g hgo]; exact hg')
    have hcard' : (disagree lam' mu).card ≤ N := by
      have h1 := Finset.card_le_card hsub
      have h2 : ((disagree lam mu).erase s).card = (disagree lam mu).card - 1 :=
        Finset.card_erase_of_mem hs
      have h3 : 1 ≤ (disagree lam mu).card := Finset.card_pos.mpr ⟨s, hs⟩
      omega
    exact (ih lam' mu hle' hcard').trans (step lam hs1 hc)

set_option linter.unusedDecidableInType false in
/-- **Increasing every rate does not increase the power sum**, given the one-orbit
step.

The hypothesis `λ_s ≤ μ_s` is imposed only off the identity; at the identity both
are `0`, so the total inequality the induction runs on follows. -/
theorem Phi_le_of_le_of_step {t : ℝ} {m : ℕ} (step : OneOrbitStep G t m)
    (lam mu : RateFn G) (hle : ∀ g : G, g ≠ 1 → lam g ≤ mu g) :
    Phi mu t m ≤ Phi lam t m := by
  refine Phi_le_of_le_aux step (disagree lam mu).card lam mu (fun g => ?_) le_rfl
  by_cases hg : g = 1
  · rw [hg, lam.apply_one, mu.apply_one]
  · exact hle g hg

end Lyons
