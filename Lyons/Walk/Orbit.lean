/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Basic

/-!
# Inverse orbits, one-rate families, and the centred power sum

The bookkeeping the final induction runs on: rates are raised one inverse orbit
at a time, and `Phi` is the quantity shown to be nonincreasing.

## Main definitions

* `Lyons.invOrbit` : `O s = {s, s⁻¹}`.
* `Lyons.Phi` : `Φ_m(λ, t) = ∑ g, ‖p_t^λ(g) - 1/|G|‖ ^ (2m)`.
-/

open Finset

namespace Lyons

variable {G : Type*} [Group G] [DecidableEq G]

/-- The **inverse orbit** of `s`, namely `{s, s⁻¹}`. -/
@[lyons_tag "def_inverse_orbit"]
def invOrbit (s : G) : Finset G := {s, s⁻¹}

@[simp] theorem mem_invOrbit {s g : G} : g ∈ invOrbit s ↔ g = s ∨ g = s⁻¹ := by
  simp [invOrbit]

/-- An inverse orbit is closed under inversion — the fact that makes raising a
rate on it preserve symmetry. -/
theorem inv_mem_invOrbit {s g : G} (h : g ∈ invOrbit s) : g⁻¹ ∈ invOrbit s := by
  rcases mem_invOrbit.mp h with rfl | rfl
  · exact mem_invOrbit.mpr (Or.inr rfl)
  · exact mem_invOrbit.mpr (Or.inl (inv_inv _))

/-- A rate function is constant on an inverse orbit — that is what symmetry says,
and it is what makes one orbit increment land exactly on the target. -/
theorem RateFn.apply_of_mem_invOrbit (lam : RateFn G) {s g : G}
    (h : g ∈ invOrbit s) : lam g = lam s := by
  rcases mem_invOrbit.mp h with rfl | rfl
  · rfl
  · exact lam.symm s

/-- The **centred power sum** `Φ_m(λ, t)`, the quantity the main theorem shows is
nonincreasing in the rates.

The coefficients are `ℂ`-valued matrix entries, so the norm is taken. This
agrees with the real power sum `∑ g ((a_t)_g) ^ (2m)` whenever the coefficients
are real, since `|x| ^ (2m) = x ^ (2m)` for even exponents. -/
@[lyons_tag "def_Phi"]
noncomputable def Phi [Fintype G] (lam : RateFn G) (t : ℝ) (m : ℕ) : ℝ :=
  ∑ g : G, ‖centeredHeatCoeff lam t g‖ ^ (2 * m)

end Lyons
