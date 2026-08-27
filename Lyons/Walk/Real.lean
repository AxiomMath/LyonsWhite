/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Orbit

/-!
# The transition function is real-valued

`heatCoeff` is defined as an entry of `exp (-t • L Δ)`, hence lands in `ℂ`. The
main theorem is about `|p_t(g) - 1/|G||^{2m}` with `p_t(g)` real, so the `ℂ`/`ℝ`
seam has to be closed before it can even be *stated*.

## The argument

Entrywise conjugation on matrices is `M ↦ (Mᴴ)ᵀ`, and Mathlib supplies
`Matrix.exp_conjTranspose` and `Matrix.exp_transpose`, so conjugation commutes
with the exponential. Since `L x` has real entries by construction, it is fixed
by conjugation, and therefore so is its exponential — which is exactly
realness of the entries. No spectral theory is involved.

## Main results

* `Lyons.conjMap_eq` : entrywise conjugation is `(Mᴴ)ᵀ`.
* `Lyons.heatMat_conj` : the heat matrix is fixed by entrywise conjugation.
* `Lyons.heatCoeff_im` / `Lyons.centeredHeatCoeff_im` : the imaginary parts vanish.
* `Lyons.heatCoeffReal` : the transition function as an `ℝ`-valued function, with
  `Lyons.heatCoeff_eq_real` identifying it with `heatCoeff`.
* `Lyons.Phi_eq_sum_real` : `Phi` as a sum of real even powers.
-/

open Matrix
open scoped ComplexConjugate

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Entrywise complex conjugation of a square matrix is the conjugate transpose
composed with the transpose. -/
theorem conjMap_eq (M : Matrix G G ℂ) :
    M.map (starRingEnd ℂ) = (Mᴴ)ᵀ := by
  ext g h
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

omit [Group G] in
/-- Entrywise conjugation commutes with the matrix exponential. -/
theorem conjMap_exp (A : Matrix G G ℂ) :
    (NormedSpace.exp A).map (starRingEnd ℂ)
      = NormedSpace.exp (A.map (starRingEnd ℂ)) := by
  rw [conjMap_eq, conjMap_eq, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose]

omit [Fintype G] [DecidableEq G] in
/-- The left regular representation has real entries, so entrywise conjugation
fixes it. -/
@[simp] theorem conjMap_L (x : MonoidAlgebra ℝ G) :
    (L x).map (starRingEnd ℂ) = L x := by
  ext g h
  simp [L_apply]

/-- The heat matrix is fixed by entrywise conjugation: its entries are real. -/
theorem heatMat_conj (lam : RateFn G) (t : ℝ) :
    (heatMat lam t).map (starRingEnd ℂ) = heatMat lam t := by
  rw [heatMat, conjMap_exp]
  congr 1
  ext g h
  simp [L_apply]

/-- **The transition function is real-valued.** -/
theorem heatCoeff_im (lam : RateFn G) (t : ℝ) (g : G) :
    (heatCoeff lam t g).im = 0 := by
  have h := congrFun (congrFun (heatMat_conj lam t) g) 1
  simp only [Matrix.map_apply, starRingEnd_apply] at h
  have := Complex.conj_eq_iff_im.mp h
  simpa [heatCoeff] using this

/-- The centered transition function is real-valued. -/
theorem centeredHeatCoeff_im (lam : RateFn G) (t : ℝ) (g : G) :
    (centeredHeatCoeff lam t g).im = 0 := by
  simp [centeredHeatCoeff, heatCoeff_im]

/-- The transition function, as an honestly `ℝ`-valued function. This is the
`p_t^λ` of the source paper. -/
@[lyons_tag "def_heat_coeff_real"]
noncomputable def heatCoeffReal (lam : RateFn G) (t : ℝ) : G → ℝ :=
  fun g => (heatCoeff lam t g).re

/-- The `ℝ`-valued and `ℂ`-valued transition functions agree: the heat
coefficient is real. -/
@[lyons_tag "lem_heat_coeff_real"]
theorem heatCoeff_eq_real (lam : RateFn G) (t : ℝ) (g : G) :
    heatCoeff lam t g = ((heatCoeffReal lam t g : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [heatCoeffReal]
  · simp [heatCoeffReal, heatCoeff_im lam t g]

/-- The centered transition function, `ℝ`-valued. -/
@[lyons_tag "def_centered_heat"]
noncomputable def centeredHeatCoeffReal (lam : RateFn G) (t : ℝ) : G → ℝ :=
  fun g => heatCoeffReal lam t g - (Fintype.card G : ℝ)⁻¹

/-- `Phi` as a sum of real even powers: with real coefficients the norm and the
even power agree, `|x| ^ (2m) = x ^ (2m)`. -/
theorem Phi_eq_sum_real (lam : RateFn G) (t : ℝ) (m : ℕ) :
    Phi lam t m = ∑ g : G, (centeredHeatCoeffReal lam t g) ^ (2 * m) := by
  rw [Phi]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  have hre : centeredHeatCoeff lam t g
      = ((centeredHeatCoeffReal lam t g : ℝ) : ℂ) := by
    rw [centeredHeatCoeff, centeredHeatCoeffReal, heatCoeff_eq_real]
    push_cast
    ring
  -- `|r| ^ (2m) = (|r|^2)^m = (r^2)^m = r ^ (2m)`, no evenness lemma needed.
  rw [hre, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs, ← pow_mul]

end Lyons
