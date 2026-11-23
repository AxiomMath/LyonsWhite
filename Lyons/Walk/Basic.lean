/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Order
public import Lyons.GroupAlgebra.Commutant

/-!
# Symmetric rate functions, the Laplacian, and the heat element

The walk-theoretic layer. A symmetric rate function determines a group-algebra
Laplacian, whose exponential is the heat element; centering by the uniform
element gives the object whose `ℓ^{2m}` norm the main theorem controls.

## Implementation notes

**Rates are defined on all of `G`, with value `0` at the identity**, rather than
on `G \ {1}`. This is not a weakening: the identity's contribution to the
Laplacian is `λ₁ • (1 - 1) = 0`, so extending a rate function by zero at `1`
changes no Laplacian and no heat element. It removes a subtype from every
downstream statement.

**The heat and centered-heat elements are coefficient functions read off the
first column**, following `Lyons.cfc_L_conv`, rather than group-algebra elements.
No group-algebra element with a prescribed left-regular matrix then has to be
constructed: the coefficient function *is* the object, and the matrix it came
from is recovered by translation invariance.

## Main definitions

* `Lyons.RateFn` : a symmetric rate function.
* `Lyons.laplacian` : `Δ_λ = ∑ s, λ s • (1 - s)`.
* `Lyons.uniform` : the uniform element `π_G`.
* `Lyons.heatCoeff` : `p_t^λ`, the coefficient function of `exp (-t Δ_λ)`.
* `Lyons.centeredHeatCoeff` : `p_t^λ - 1/|G|`.
-/

@[expose] public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace RateFn

section
variable {G : Type*} [Group G]

@[simp] theorem coe_mk (f : G → ℝ) (h₁ h₂ h₃) :
    ((⟨f, h₁, h₂, h₃⟩ : RateFn G) : G → ℝ) = f := rfl

theorem nonneg (lam : RateFn G) (g : G) : 0 ≤ lam g := lam.nonneg' g

theorem symm (lam : RateFn G) (g : G) : lam g⁻¹ = lam g := lam.symm' g

@[simp] theorem apply_one (lam : RateFn G) : lam 1 = 0 := lam.atOne

end

end RateFn

/-- The **uniform element** `π_G`, with every coefficient `1/|G|`. -/
@[lyons_tag "def_uniform"]
noncomputable def uniform (G : Type*) [Group G] [Fintype G] : MonoidAlgebra ℝ G :=
  ∑ g : G, MonoidAlgebra.single g ((Fintype.card G : ℝ)⁻¹)

/-- The **centered** transition function, `p_t^λ(g) - 1/|G|`. -/
noncomputable def centeredHeatCoeff (lam : RateFn G) (t : ℝ) : G → ℂ :=
  fun g => heatCoeff lam t g - ((Fintype.card G : ℝ) : ℂ)⁻¹

/-- Coefficients of the centered heat element. This is definitional, since
`centeredHeatCoeff` is *defined* by subtracting `1/|G|` from `heatCoeff`. -/
@[lyons_tag "lem_centered_coeff", simp]
theorem centeredHeatCoeff_apply (lam : RateFn G) (t : ℝ) (g : G) :
    centeredHeatCoeff lam t g = heatCoeff lam t g - ((Fintype.card G : ℝ) : ℂ)⁻¹ :=
  rfl

omit [DecidableEq G] in
/-- Coefficients of the uniform element. -/
@[simp] theorem coe_uniform (g : G) :
    co (uniform G) g = (Fintype.card G : ℝ)⁻¹ := by
  classical
  simp [co, uniform, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]

end Lyons
