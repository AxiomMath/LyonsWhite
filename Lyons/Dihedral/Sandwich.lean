/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Pos

/-!
# The reflection sandwich

For positive `a` and `θ ∈ (0,1)` the sandwich is the group-algebra element whose
left regular matrix is
`(L a) ^ θ * L b * (L a) ^ (1 - θ)`.

The construction is the same three-step pattern used for the square root: the
matrix product is a left convolution (each factor commutes with every right
translation), its entries are real (each factor has real entries), so the first
column defines a group-algebra element with that matrix.

## Main definitions

* `Lyons.sandwichMat` : the matrix product.
* `Lyons.sandwich` : the group-algebra element.
-/

open Matrix DihedralGroup
open scoped ComplexOrder MatrixOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The sandwich, as a matrix. -/
noncomputable def sandwichMat (x : MonoidAlgebra ℝ G) (b : G) (θ : ℝ) :
    Matrix G G ℂ :=
  mpow (L x) θ * L (MonoidAlgebra.single b (1 : ℝ)) * mpow (L x) (1 - θ)

/-- The sandwich matrix commutes with every right translation, being a product of
three matrices that each do. -/
theorem sandwichMat_commutes (x : MonoidAlgebra ℝ G) (b : G) (θ : ℝ) (h : G) :
    Commute (sandwichMat x b θ) (R h) := by
  have h1 : ∀ t : ℝ, Commute (mpow (L x) t) (R h) := fun t =>
    Commute.cfc_real (show Commute (L x) (R h) from L_commutes_R x h) _
  have h2 : Commute (L (MonoidAlgebra.single b (1 : ℝ))) (R h) :=
    L_commutes_R _ h
  rw [sandwichMat]
  exact Commute.mul_left (Commute.mul_left (h1 θ) h2) (h1 (1 - θ))

/-- Hence its entries depend only on `g * g'⁻¹`. -/
theorem sandwichMat_conv (x : MonoidAlgebra ℝ G) (b : G) (θ : ℝ) (g g' : G) :
    sandwichMat x b θ g g' = sandwichMat x b θ (g * g'⁻¹) 1 :=
  (commutes_R_iff _).mp (sandwichMat_commutes x b θ) g g'

/-- The sandwich matrix is fixed by entrywise conjugation: all three factors are.
`conjHom` is multiplicative, so this is where being a *homomorphism* (rather than
merely commuting with `cfc`) earns its keep. -/
theorem conjHom_sandwichMat (x : MonoidAlgebra ℝ G) (hx : IsPos x) (b : G)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    conjHom (sandwichMat x b θ) = sandwichMat x b θ := by
  have hle : (0 : Matrix G G ℂ) ≤ L x := (isPos_iff_le x).mp hx
  have hsa : IsSelfAdjoint (L x) := (Matrix.nonneg_iff_posSemidef.mp hle).isHermitian
  have hc : ContinuousOn (fun t : ℝ => t ^ θ) (spectrum ℝ (L x)) :=
    (Real.continuous_rpow_const hθ).continuousOn
  have hc' : ContinuousOn (fun t : ℝ => t ^ (1 - θ)) (spectrum ℝ (L x)) :=
    (Real.continuous_rpow_const (by linarith)).continuousOn
  rw [sandwichMat, map_mul, map_mul, mpow, mpow,
    conjHom_cfc_L x _ hc hsa, conjHom_cfc_L x _ hc' hsa, conjHom_L]

/-- **The reflection sandwich**, as a group-algebra element. -/
@[lyons_tag "def_sandwich"]
noncomputable def sandwich (x : MonoidAlgebra ℝ G) (b : G) (θ : ℝ) :
    MonoidAlgebra ℝ G :=
  ofFun (fun g => (sandwichMat x b θ g 1).re)

/-- The left regular matrix of the sandwich element is the sandwich matrix. -/
theorem L_sandwich (x : MonoidAlgebra ℝ G) (hx : IsPos x) (b : G) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    L (sandwich x b θ) = sandwichMat x b θ := by
  ext g h
  have hreal : (sandwichMat x b θ (g * h⁻¹) 1).im = 0 := by
    have := congrFun (congrFun (conjHom_sandwichMat x hx b hθ hθ') (g * h⁻¹)) 1
    rw [conjHom_apply, starRingEnd_apply] at this
    exact Complex.conj_eq_iff_im.mp this
  rw [L_apply, sandwich, co_ofFun, sandwichMat_conv x b θ g h]
  apply Complex.ext <;> simp [hreal]

/-- **The sandwich is a product inside the group algebra.** The definition builds
it from a matrix column, so nothing about it is manifestly algebraic; this says
it is exactly `a^θ · b · a^{1-θ}` with all three factors group-algebra elements.

This is what makes the sandwich visible to *other* representations: an algebra
homomorphism can be applied to a product, but not to a matrix column. -/
theorem sandwich_eq_mul (x : MonoidAlgebra ℝ G) (hx : IsPos x) (b : G) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    sandwich x b θ
      = powElt x θ * MonoidAlgebra.single b (1 : ℝ) * powElt x (1 - θ) := by
  refine L_injective ?_
  rw [L_sandwich x hx b hθ hθ', L_mul, L_mul, L_powElt x hx hθ,
    L_powElt x hx (by linarith : (0 : ℝ) ≤ 1 - θ), sandwichMat]

end Lyons
