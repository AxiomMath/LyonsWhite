/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.Basic
import Lyons.Walk.CentralStep

/-!
# Increments inside the abelian part are central, and raising them is free

Over the inversion extension `G_{A,z}`, this is the elementary half of
`Lyons.rateMonotonic_invExt_even`: because `ζ_{ι a}` is central, the two
generators commute, the exponentials
factor, and the new centred heat element is the old one convolved with a
probability element — no Duhamel formula and no integral. Elements outside the
abelian part have no such property, and that asymmetry *is* the difficulty of the
paper.

## The mechanism

`Lyons.orbitElt_central_of_conj_stable` reduces centrality to stability of the
inverse orbit `O(ι a) = {ι a, ι (-a)}` under conjugation, and that is the
extension's two conjugation rules: `ι a'` centralizes `ι a` because `A` is
abelian (`InvExt.rot_mul_rot`), and `ι d τ` inverts it (`InvExt.refl_conj`), so
it swaps the two orbit members. Note that `z` plays no role: the orbit is stable
whatever `z` is.

`Lyons.Phi_addOrbit_le_of_central` then supplies the whole analytic argument,
which is group-generic.

## Main results

* `Lyons.conj_mem_invOrbit_rot` : the orbit of `ι a` is conjugation-stable.
* `Lyons.orbitElt_central_rot` : increments inside the abelian part are central.
* `Lyons.Phi_addOrbit_rot_le` : increasing a rate inside the abelian part does
  not increase the power sum.
-/

open Finset

namespace Lyons

variable {A : Type*} [AddCommGroup A] {z : A} [Fact (z + z = 0)]

/-- Conjugation sends `ι a` into its own inverse orbit: an element of the abelian
part centralizes it, and an element outside inverts it. -/
theorem conj_rot (g : InvExt A z) (a : A) :
    g * InvExt.rot a * g⁻¹ = InvExt.rot a ∨
      g * InvExt.rot a * g⁻¹ = InvExt.rot (-a) := by
  cases g with
  | rot a' =>
    left
    rw [InvExt.inv_rot, InvExt.rot_mul_rot, InvExt.rot_mul_rot]
    congr 1
    abel
  | refl d => exact Or.inr (InvExt.refl_conj d a)

variable [DecidableEq A]

/-- The inverse orbit of `ι a` is stable under conjugation, which is what makes
its orbit sum central. -/
theorem conj_mem_invOrbit_rot {a : A} {x : InvExt A z}
    (hx : x ∈ invOrbit (InvExt.rot a : InvExt A z)) (g : InvExt A z) :
    g * x * g⁻¹ ∈ invOrbit (InvExt.rot a : InvExt A z) := by
  have hinv : (InvExt.rot a : InvExt A z)⁻¹ = InvExt.rot (-a) := InvExt.inv_rot a
  rcases mem_invOrbit.mp hx with rfl | rfl
  · rcases conj_rot g a with h | h
    · exact mem_invOrbit.mpr (Or.inl h)
    · exact mem_invOrbit.mpr (Or.inr (by rw [hinv]; exact h))
  · rw [hinv]
    rcases conj_rot g (-a) with h | h
    · exact mem_invOrbit.mpr (Or.inr (by rw [hinv]; exact h))
    · exact mem_invOrbit.mpr (Or.inl (by rwa [neg_neg] at h))

variable [Fintype A]

set_option linter.unusedFintypeInType false in
/-- **Increments inside the abelian part are central.** -/
@[lyons_tag "lem_rotation_central"]
theorem orbitElt_central_rot (a : A) (y : MonoidAlgebra ℝ (InvExt A z)) :
    orbitElt (InvExt.rot a : InvExt A z) * y
      = y * orbitElt (InvExt.rot a : InvExt A z) :=
  orbitElt_central_of_conj_stable (fun _ hx g => conj_mem_invOrbit_rot hx g) y

set_option linter.unusedDecidableInType false in
/-- **Increasing a rate inside the abelian part does not increase the power
sum.**

The analytic content is group-generic (`Lyons.Phi_addOrbit_le_of_central`); all
this adds is centrality. -/
@[lyons_tag "lem_rotation_step"]
theorem Phi_addOrbit_rot_le (lam : RateFn (InvExt A z)) (a : A)
    (hs1 : (InvExt.rot a : InvExt A z) ≠ 1) {c : ℝ} (hc : 0 ≤ c) {t : ℝ}
    (ht : 0 ≤ t) (m : ℕ) :
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m :=
  Phi_addOrbit_le_of_central (orbitElt_central_rot a) lam hs1 hc ht m

end Lyons
