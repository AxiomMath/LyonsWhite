/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.Notation
import Lyons.Fourier.Parseval
import Lyons.GroupAlgebra.Basic

/-!
# The two-dimensional representations of the dihedral group

For each `k : ZMod n` the assignment

* `r j  ↦  diag (χ (k j), χ (-k j))`
* `sr j ↦  ![![0, χ (-k j)], ![χ (k j), 0]]`

is a monoid homomorphism `DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ`, where
`χ = ZMod.stdAddChar`. This is the cyclic special case of the construction
carried out for the inversion extension `G_{A,z}` by
`Lyons.InvExtBlock.rho`.

## A sign convention that is easy to get wrong

Mathlib's second constructor satisfies `r_mul_sr : r i * sr j = sr (j - i)`, so
taking `j = 0` gives `sr (-i) = r i * sr 0`; that is, **`sr j = r ^ (-j) * b`**
with `b = sr 0`, not `r ^ j * b`. Consequently the off-diagonal entries carry
`χ (-k j)` in the upper-right and `χ (k j)` in the lower-left — the opposite of
what a direct transcription of `ρ_k(r^j b)` would give. With the naive
assignment `map_mul'` is false, and only in the two mixed cases, so it would not
be caught by a spot check on rotations.

`χ` is used rather than a literal `exp (2 π i / n)` so that this file shares the
character API already established for the Fourier work — `AddChar.map_add_eq_mul`
does all the arithmetic.
-/

open Matrix DihedralGroup

namespace Lyons

variable {n : ℕ} [NeZero n]

/-- Products of character values add their arguments. -/
theorem chi_mul (a b : ZMod n) :
    (ZMod.stdAddChar a : ℂ) * ZMod.stdAddChar b = ZMod.stdAddChar (a + b) :=
  (AddChar.map_add_eq_mul _ _ _).symm

/-- The underlying function of the `k`-th two-dimensional representation. -/
noncomputable def rhoFun (k : ZMod n) :
    DihedralGroup n → Matrix (Fin 2) (Fin 2) ℂ
  | .r j => !![(ZMod.stdAddChar (k * j) : ℂ), 0; 0, (ZMod.stdAddChar (-(k * j)) : ℂ)]
  | .sr j => !![0, (ZMod.stdAddChar (-(k * j)) : ℂ); (ZMod.stdAddChar (k * j) : ℂ), 0]

@[simp] theorem rhoFun_r (k j : ZMod n) :
    rhoFun k (.r j)
      = !![(ZMod.stdAddChar (k * j) : ℂ), 0; 0, (ZMod.stdAddChar (-(k * j)) : ℂ)] :=
  rfl

@[simp] theorem rhoFun_sr (k j : ZMod n) :
    rhoFun k (.sr j)
      = !![0, (ZMod.stdAddChar (-(k * j)) : ℂ); (ZMod.stdAddChar (k * j) : ℂ), 0] :=
  rfl

/-- **The `k`-th two-dimensional representation** of `DihedralGroup n`. The
content is that `rhoFun` respects the dihedral multiplication table, which is
what bundling it as a `MonoidHom` records.

The general version, over the inversion extension `G_{A,z}` and indexed by a
*character* of a finite abelian `A` together with a distinguished outside
element, is `Lyons.InvExtBlock.rho`; this is its cyclic special case. -/
noncomputable def rho (k : ZMod n) :
    DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := rhoFun k
  map_one' := by
    rw [one_def, rhoFun_r, mul_zero, neg_zero]
    simp only [AddChar.map_zero_eq_one]
    exact Matrix.one_fin_two.symm
  map_mul' x y := by
    cases x with
    | r i =>
      cases y with
      | r j =>
        rw [r_mul_r, rhoFun_r, rhoFun_r, rhoFun_r]
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, chi_mul] <;>
          congr 1 <;> ring
      | sr j =>
        rw [r_mul_sr, rhoFun_r, rhoFun_sr, rhoFun_sr]
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, chi_mul] <;>
          congr 1 <;> ring
    | sr i =>
      cases y with
      | r j =>
        rw [sr_mul_r, rhoFun_sr, rhoFun_r, rhoFun_sr]
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, chi_mul] <;>
          congr 1 <;> ring
      | sr j =>
        rw [sr_mul_sr, rhoFun_sr, rhoFun_sr, rhoFun_r]
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, chi_mul] <;>
          congr 1 <;> ring


@[simp] theorem rho_apply_r (k j : ZMod n) :
    rho k (.r j)
      = !![(ZMod.stdAddChar (k * j) : ℂ), 0; 0, (ZMod.stdAddChar (-(k * j)) : ℂ)] :=
  rfl

@[simp] theorem rho_apply_sr (k j : ZMod n) :
    rho k (.sr j)
      = !![0, (ZMod.stdAddChar (-(k * j)) : ℂ); (ZMod.stdAddChar (k * j) : ℂ), 0] :=
  rfl

/-! ### Extension to the group algebra, and star-preservation -/

/-- Conjugating a character value negates its argument. -/
theorem conj_chi (a : ZMod n) :
    (starRingEnd ℂ) (ZMod.stdAddChar a : ℂ) = ZMod.stdAddChar (-a) :=
  ZMod.conj_stdAddChar a

/-- Each `rho k g` is unitary: inverses go to conjugate transposes. This is the
group-level half of star-preservation. -/
theorem rho_inv (k : ZMod n) (g : DihedralGroup n) :
    rho k g⁻¹ = (rho k g)ᴴ := by
  cases g with
  | r j =>
    rw [show (DihedralGroup.r j)⁻¹ = DihedralGroup.r (-j) from rfl]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.conjTranspose_apply, conj_chi, mul_neg]
  | sr j =>
    rw [show (DihedralGroup.sr j)⁻¹ = DihedralGroup.sr j from rfl]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.conjTranspose_apply, conj_chi, neg_neg]

/-- The `k`-th representation extended to the real group algebra, as an
`ℝ`-algebra homomorphism. The general version is `Lyons.InvExtBlock.rhoAlg`. -/
noncomputable def rhoAlg (k : ZMod n) :
    MonoidAlgebra ℝ (DihedralGroup n) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  MonoidAlgebra.lift ℝ (Matrix (Fin 2) (Fin 2) ℂ) (DihedralGroup n) (rho k)

@[simp] theorem rhoAlg_single (k : ZMod n) (g : DihedralGroup n) (c : ℝ) :
    rhoAlg k (MonoidAlgebra.single g c) = c • rho k g :=
  MonoidAlgebra.lift_single (rho k) g c

/-- **`rho` is star-preserving on the group algebra.** Together with `rhoAlg`
being an `ℝ`-algebra homomorphism this is the statement that `ρ_k` is a unital
`*`-representation.

The proof reduces to `rho_inv` on basis elements: `invol` sends `g` to `g⁻¹`
without conjugating (the coefficients are real), and `rho_inv` says each
`rho k g` is unitary.

The general finite abelian version is `Lyons.InvExtBlock.rhoAlg_invol`. -/
theorem rhoAlg_invol (k : ZMod n) (x : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k (invol x) = (rhoAlg k x)ᴴ := by
  classical
  -- Freeze the coefficient function first: rewriting with `hx` below must not
  -- reach the `co x g` occurrences inside it.
  set c : DihedralGroup n → ℝ := co x with hc
  -- Expand both sides over the basis.
  have hx : x = ∑ g : DihedralGroup n, MonoidAlgebra.single g (c g) := by
    refine co_injective fun h ↦ ?_
    rw [co_sum]
    rw [Finset.sum_eq_single h]
    · simp [hc]
    · intro b _ hb; simp [Ne.symm hb]
    · intro hcon; exact absurd (Finset.mem_univ h) hcon
  have hinv : invol x
      = ∑ g : DihedralGroup n, MonoidAlgebra.single g⁻¹ (c g) := by
    refine co_injective fun h ↦ ?_
    rw [co_invol, co_sum]
    rw [Finset.sum_eq_single h⁻¹]
    · simp [hc]
    · intro b _ hb
      have : h ≠ b⁻¹ := fun hcon => hb (by rw [hcon, inv_inv])
      simp [this]
    · intro hcon; exact absurd (Finset.mem_univ h⁻¹) hcon
  rw [hinv, hx, map_sum, map_sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [rhoAlg_single, rhoAlg_single, rho_inv, Matrix.conjTranspose_smul]
  simp

end Lyons
