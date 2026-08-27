/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Real

/-!
# Coefficients of the Laplacian, and absorption by the uniform element

## Main results

* `Lyons.coe_laplacian` : `Δ_λ` has coefficient `Λ - λ 1` at the identity and
  `-λ g` elsewhere, where `Λ = ∑ s, λ s`.
* `Lyons.laplacian_invol` : `Δ_λ` is self-adjoint.
* `Lyons.uniform_absorb` : `x * π_G = (∑ g, x g) • π_G`.
* `Lyons.uniform_idem` : `π_G` is idempotent.
-/

open Finset

namespace Lyons


section
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

-- `DecidableEq G` is genuinely required by the coefficient computations these
-- proofs invoke (`coe_laplacian`, `MonoidAlgebra.coeff_mul_apply_right`), but
-- Lean sees it used only inside the proof terms, not in the statements. Omitting
-- it breaks elaboration, and the linter's suggested `open scoped Classical` would
-- substitute a decidability instance different from the one `Lyons.L` and
-- `Lyons.uniform` were built with, risking instance mismatch. So the two
-- unused-hypothesis checks are disabled for this section only.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-! ### The Laplacian -/

/-- Coefficients of the Laplacian: the total rate at the identity, `-λ g`
elsewhere. -/
theorem coe_laplacian (lam : RateFn G) (g : G) :
    co (laplacian lam) g = (if g = 1 then ∑ s : G, lam s else 0) - lam g := by
  classical
  rw [laplacian, co_sum]
  have hterm : ∀ s : G, co (lam s • (1 - MonoidAlgebra.single s (1 : ℝ))) g
      = lam s * (if g = 1 then (1 : ℝ) else 0)
        - lam s * (if g = s then (1 : ℝ) else 0) := by
    intro s
    simp [mul_sub]
  rw [Finset.sum_congr rfl fun s _ ↦ hterm s, Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_mul]
    by_cases hg : g = 1 <;> simp [hg]
  · rw [Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hcon
      exact absurd (Finset.mem_univ g) hcon

/-- **The Laplacian is self-adjoint.** -/
@[lyons_tag "lem_laplacian_star"]
theorem laplacian_invol (lam : RateFn G) : invol (laplacian lam) = laplacian lam := by
  refine co_injective fun g ↦ ?_
  rw [co_invol, coe_laplacian, coe_laplacian, lam.symm]
  congr 1
  simp [inv_eq_one]

/-! ### Absorption by the uniform element -/

/-- Coefficients of `x * π_G`: every one is the coefficient sum of `x`, divided
by `|G|`. -/
theorem coe_mul_uniform (x : MonoidAlgebra ℝ G) (g : G) :
    co (x * uniform G) g = (∑ h : G, co x h) * (Fintype.card G : ℝ)⁻¹ := by
  classical
  rw [co_mul]
  simp only [coe_uniform]
  rw [← Finset.sum_mul]
  congr 1
  -- Reindex by `h ↦ g * h⁻¹`, a bijection of `G`.
  exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft g)) _ _ fun h ↦ rfl

/-- **Absorption**: multiplying by `π_G` collapses `x` to its coefficient sum. -/
@[lyons_tag "lem_uniform_absorb"]
theorem uniform_absorb (x : MonoidAlgebra ℝ G) :
    x * uniform G = (∑ h : G, co x h) • uniform G := by
  refine co_injective fun g ↦ ?_
  rw [coe_mul_uniform, co_smul, coe_uniform]

/-- **The uniform element is idempotent.** -/
@[lyons_tag "lem_uniform_idem"]
theorem uniform_idem : uniform G * uniform G = uniform G := by
  classical
  have hcard : (Fintype.card G : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [uniform_absorb]
  have hsum : ∑ h : G, co (uniform G) h = 1 := by
    simp only [coe_uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hsum, one_smul]

end

end Lyons
