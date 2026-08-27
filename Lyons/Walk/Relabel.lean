/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Laplacian

/-!
# Relabelling a rate function along a group isomorphism

The dihedral group and the inversion extension `G_{ℤ/n, 0}` are two descriptions
of one group, so in Lean they are two different objects and the conclusion of
`Lyons.rateMonotonic_invExt_even` has to be carried from one to the other. This
file supplies the transport, for an arbitrary isomorphism `φ : H ≃* G` of finite
groups.

## How the transport is proved

Not by building the induced algebra isomorphism of `ℝ[G]`, which would need its
multiplicativity proved. Instead `Lyons.coe_laplacian` writes the Laplacian's
coefficients out in closed form, from which `L (Δ_{λ^φ})` is visibly `L (Δ_λ)`
with rows and columns permuted by `φ`. Reindexing is an algebra isomorphism of the
matrix algebra and is continuous, so it commutes with the exponential
(`NormedSpace.map_exp`), and reading off column one gives the transported
transition function.

## Main results

* `Lyons.RateFn.comp` : `λ^φ`, the relabelled rate function.
* `Lyons.heatCoeff_comp` : the transition function transports.
* `Lyons.Phi_comp` : the centred power sum is unchanged.
-/
open Matrix
-- The operator norm on matrices is `scoped`, and `NormedSpace.map_exp` needs the
-- `NormedRing` instance it provides. Mathlib's own matrix-exponential lemmas open
-- exactly this scope, per lemma; opening it here does not touch the `‖·‖` on `ℂ`
-- that `Lyons.Phi` uses.
open scoped Norms.Operator

namespace Lyons

/-! ### The relabelled rate function

Nothing in this section is analytic, so it is kept free of `Fintype G`: otherwise
the simp lemma below carries an instance it does not use, and every consumer has
to supply one. -/

section Rate

variable {G H : Type*} [Group G] [Group H] [DecidableEq G]

/-- **The relabelled rate function** `λ^φ`, with `λ^φ h = λ (φ h)`.

Stated for an isomorphism `φ : H ≃* G` between two possibly different groups,
which is the form the passage from the inversion extension to the dihedral group
needs; the dihedral route uses it at `H = G` with an automorphism.

Rates here are defined on all of `G` with value `0` at the identity, so no
side condition is needed to see that this lands in the right domain; an
isomorphism fixes the identity, which is what `atOne` uses. -/
@[lyons_tag "def_rate_comp"]
def RateFn.comp (lam : RateFn G) (φ : H ≃* G) : RateFn H where
  toFun g := lam (φ g)
  nonneg' g := lam.nonneg _
  symm' g := by rw [map_inv, lam.symm]
  atOne := by rw [map_one, lam.apply_one]

omit [DecidableEq G] in
@[simp] theorem RateFn.comp_apply (lam : RateFn G) (φ : H ≃* G) (h : H) :
    lam.comp φ h = lam (φ h) := rfl

omit [DecidableEq G] in
/-- **The relabelled function is a symmetric rate function.**

This is discharged by `RateFn.comp`'s own construction, because `RateFn G` *is*
the type of symmetric rate functions: the claim lives in that definition's type
rather than in a separate proposition. This spells the three conditions out. -/
@[lyons_tag "lem_rate_comp_symmetric"]
theorem RateFn.comp_isRate (lam : RateFn G) (φ : H ≃* G) :
    (∀ h : H, 0 ≤ lam.comp φ h) ∧ (∀ h : H, lam.comp φ h⁻¹ = lam.comp φ h) ∧
      lam.comp φ 1 = 0 :=
  ⟨fun g => (lam.comp φ).nonneg g, fun g => (lam.comp φ).symm g,
    (lam.comp φ).apply_one⟩

end Rate

/-! ### The Laplacian in coordinates -/

section Transport

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H]

set_option linter.unusedDecidableInType false in
/-- Relabelling the rate function relabels the Laplacian's coefficients. -/
theorem co_laplacian_comp (lam : RateFn G) (φ : H ≃* G) (u : H) :
    co (laplacian (lam.comp φ)) u = co (laplacian lam) (φ u) := by
  have hsum : ∑ s : H, lam.comp φ s = ∑ s : G, lam s :=
    Fintype.sum_equiv φ.toEquiv _ _ fun s => by simp
  rw [coe_laplacian, coe_laplacian, RateFn.comp_apply, hsum]
  by_cases hu : u = 1
  · subst hu; simp
  · have hφu : φ u ≠ 1 := fun h => hu (by simpa using φ.injective (h.trans (map_one φ).symm))
    simp [hu, hφu]

/-! ### Transport along the reindexing

`Matrix.reindex e e` with `e = φ⁻¹` sends a matrix `A` to `fun g h => A (φ g) (φ h)`;
that is the direction the coefficient calculation produces. -/

omit [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] in
/-- Reindexing rows and columns is continuous: each entry of the image is one
entry of the argument. This discharges `NormedSpace.map_exp`'s side condition,
which is not automatic for a map assembled here. -/
theorem continuous_reindex (e : G ≃ H) :
    Continuous (Matrix.reindex e e : Matrix G G ℂ → Matrix H H ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply (e.symm j)).comp (continuous_apply (e.symm i))

set_option linter.unusedDecidableInType false in
/-- The left regular matrix of the relabelled Laplacian is the original one with
rows and columns permuted by `φ`. -/
theorem L_laplacian_comp (lam : RateFn G) (φ : H ≃* G) :
    L (laplacian (lam.comp φ))
      = Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm (L (laplacian lam)) := by
  ext g h
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, L_apply, L_apply,
    co_laplacian_comp]
  congr 2
  simp [map_mul, map_inv]

omit [Group G] [Group H] in
/-- **Reindexing rows and columns commutes with the exponential.**

`NormedSpace.map_exp` supplies the mathematics, but it carries continuity as a
hypothesis and that is not discharged automatically for a map assembled here
rather than found in the library — `Lyons.continuous_reindex` is the obligation,
and it is why this is a lemma with a proof and not a citation. -/
@[lyons_tag "lem_ext_exp_reindex"]
theorem exp_reindex (e : G ≃ H) (A : Matrix G G ℂ) :
    NormedSpace.exp (Matrix.reindex e e A)
      = Matrix.reindex e e (NormedSpace.exp A) :=
  (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom
    (continuous_reindex _) A).symm

/-- The heat matrix transports: reindexing commutes with the exponential. -/
theorem heatMat_comp (lam : RateFn G) (φ : H ≃* G) (t : ℝ) :
    heatMat (lam.comp φ) t
      = Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm (heatMat lam t) := by
  have hsmul : (-(t : ℂ)) •
        Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm (L (laplacian lam))
      = Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm
          ((-(t : ℂ)) • L (laplacian lam)) := rfl
  rw [heatMat, heatMat, L_laplacian_comp, hsmul]
  exact exp_reindex _ _

/-- **The transition function transports along a relabelling**, on the
`ℂ`-valued coefficient. -/
theorem heatCoeff_comp (lam : RateFn G) (φ : H ≃* G) (t : ℝ) (h : H) :
    heatCoeff (lam.comp φ) t h = heatCoeff lam t (φ h) := by
  rw [heatCoeff, heatCoeff, heatMat_comp, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp

/-- **The transition function transports along a relabelling.** -/
@[lyons_tag "lem_heat_relabel"]
theorem heatCoeffReal_comp (lam : RateFn G) (φ : H ≃* G) (t : ℝ) (h : H) :
    heatCoeffReal (lam.comp φ) t h = heatCoeffReal lam t (φ h) := by
  rw [heatCoeffReal, heatCoeffReal, heatCoeff_comp]

/-- **The centred power sum is unchanged by a relabelling.**

The summands correspond term by term under `φ`, and `φ` is a bijection of `G`,
so the sums agree. -/
theorem Phi_comp (lam : RateFn G) (φ : H ≃* G) (t : ℝ) (m : ℕ) :
    Phi (lam.comp φ) t m = Phi lam t m := by
  have hcard : Fintype.card H = Fintype.card G := Fintype.card_congr φ.toEquiv
  rw [Phi, Phi]
  refine Fintype.sum_equiv φ.toEquiv _ _ fun h => ?_
  have hce : centeredHeatCoeff (lam.comp φ) t h
      = centeredHeatCoeff lam t (φ.toEquiv h) := by
    rw [centeredHeatCoeff, centeredHeatCoeff, heatCoeff_comp, hcard]
    rfl
  rw [hce]

end Transport

end Lyons
