/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Block
import Lyons.GroupAlgebra.Sqrt

/-!
# Representations preserve positivity

`ρ_k` is a representation unrelated to `L`, so positivity of `x` — which is
*defined* through `L x` — cannot be transported along `rhoAlg` by any general
star-hom argument. What makes it transferable is the factorisation
`x = y⋆ y` **inside the group algebra** (`Lyons.eq_invol_mul_self`): a star
homomorphism sends that to `ρ_k(y)ᴴ ρ_k(y)`, which is positive semidefinite for
any representation whatsoever.

## Main results

* `Lyons.rhoAlg_posSemidef`
* `Lyons.Ublock_ge_norm_Vblock`

Both are the cyclic special cases of `Lyons.InvExtBlock.rhoAlg_posSemidef` and
`Lyons.InvExtBlock.Ublock_ge_norm_Vblock`, proved for the inversion extension
`G_{A,z}`.
-/

open Matrix DihedralGroup
open scoped ComplexOrder MatrixOrder

namespace Lyons

variable {n : ℕ} [NeZero n]

/-- **Representations preserve positivity.** The general finite abelian version
is `Lyons.InvExtBlock.rhoAlg_posSemidef`. -/
theorem rhoAlg_posSemidef (k : ZMod n) (x : MonoidAlgebra ℝ (DihedralGroup n))
    (hx : IsPos x) : (rhoAlg k x).PosSemidef := by
  rw [eq_invol_mul_self x hx, map_mul, rhoAlg_invol]
  exact Matrix.posSemidef_conjTranspose_mul_self _

-- The two `simp` calls below expand a `2 × 2` matrix literal applied to a test
-- vector. Pinning them to `simp only` requires enumerating the `!![…]` entry
-- lemmas, which is brittle, so the flexible-tactic style check is disabled for
-- this declaration rather than worked around.
set_option linter.flexible false in
/-- **Positivity dominates the reflection transform.** The general finite abelian
inequality is `Lyons.InvExtBlock.Ublock_ge_norm_Vblock`.

For positive self-adjoint `a` the block is the Hermitian matrix
`![![U, V], ![conj V, U]]`, whose eigenvalues are `U ± ‖V‖`; nonnegativity of the
smaller one is the claim. The proof tests the quadratic form against
`![V/‖V‖, -1]`, chosen so that both off-diagonal contributions become `-‖V‖`
rather than an unhelpful complex number. -/
theorem Ublock_ge_norm_Vblock (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n))
    (hpos : IsPos a) (hsa : invol a = a) :
    ‖Vblock a k‖ ≤ (Ublock a k).re := by
  have hPSD := rhoAlg_posSemidef k a hpos
  have hM : rhoAlg k a
      = !![Ublock a k, Vblock a k;
           (starRingEnd ℂ) (Vblock a k), Ublock a k] :=
    rhoAlg_block_selfAdjoint k a hsa
  by_cases hV : Vblock a k = 0
  · -- Only `0 ≤ U` is needed; test against the first basis vector.
    have h0 := hPSD.dotProduct_mulVec_nonneg (![1, 0] : Fin 2 → ℂ)
    rw [hM] at h0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    rw [hV, norm_zero]
    exact (Complex.nonneg_iff.mp h0).1
  · have hVpos : (0 : ℝ) < ‖Vblock a k‖ := norm_pos_iff.mpr hV
    have h := hPSD.dotProduct_mulVec_nonneg
      (![Vblock a k / (‖Vblock a k‖ : ℂ), -1] : Fin 2 → ℂ)
    rw [hM] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    -- `conj V * V = ‖V‖ ^ 2` is what collapses the two off-diagonal terms.
    have hsq : (starRingEnd ℂ) (Vblock a k) * Vblock a k
        = ((‖Vblock a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj']
      norm_cast
    have hne : ((‖Vblock a k‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using hVpos.ne'
    have hexp :
        (starRingEnd ℂ) (Vblock a k) / ((‖Vblock a k‖ : ℝ) : ℂ) *
            (Ublock a k * (Vblock a k / ((‖Vblock a k‖ : ℝ) : ℂ)) + -Vblock a k) +
          (Ublock a k + -((starRingEnd ℂ) (Vblock a k) *
            (Vblock a k / ((‖Vblock a k‖ : ℝ) : ℂ))))
          = 2 * Ublock a k - 2 * ((‖Vblock a k‖ : ℝ) : ℂ) := by
      field_simp
      rw [hsq]
      push_cast
      ring
    rw [hexp] at h
    have hre := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
    norm_num at hre
    linarith

end Lyons
