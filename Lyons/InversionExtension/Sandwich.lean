/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Analysis.Holder
import Lyons.Dihedral.SandwichBlock
import Lyons.Fourier.AddCharEvenPart
import Lyons.InversionExtension.Blocks

/-!
# The block form of the reflection sandwich over an inversion extension

For positive self-adjoint `x ∈ ℝ[G_{A,z}]`, a real `θ ∈ [0,1]` and an outside
element `ι d * τ = InvExt.refl d`, the sandwich is `x^θ · (ι d τ) · x^{1-θ}`.
This file computes its image under `ρ_{χ,d}`.

## The split on `χ z`

`Bchi χ z = !![0, χ z; 1, 0]` is where the involution enters, and the sandwich
computation is the first place the two signs give genuinely different matrices:

* `χ z = 1` (`rhoAlg_sandwich`) is the dihedral computation. `Bchi` is the swap,
  `ρ_{χ,d}(x)` is a block `!![U, ζw; ζ̄w, U]` with `w = ‖V^{x,d}(χ)‖`, and the
  four-entry product of `Lyons.blockM_cfc_rpow` at `θ` and at `1 - θ` gives the
  stated matrix.
* `χ z = -1` (`rhoAlg_sandwich_odd`) has no dihedral analogue. There
  `Vblock_eq_zero` makes the off-diagonal block vanish, so
  `ρ_{χ,d}(x)` is the *scalar* `U^x(χ)`, its fractional powers are `U^θ` and
  `U^{1-θ}` — which multiply back to `U` because `U ≥ 0` — and `Bchi` is the
  quarter-turn `!![0, -1; 1, 0]`. The whole sandwich is `U · Bchi`.

The two consequences the layer above needs, `re_Ublock_sandwich` and
`norm_Vblock_sandwich_le`, hold on both branches and are proved by case analysis
on `char_involution`. On the odd branch they are degenerate rather than
interpolated: the source's `Q_χ = 0` is the vanishing upper-left entry, matched
by `V^{x,d}(χ) = 0` on the other side, and the source's `Y_χ = U_χ` saturates
`|Y| ≤ U`.

## What is reused rather than restated

Four layers below are already group-generic and are imported, not duplicated:

* `Lyons.sandwich` and `Lyons.sandwich_eq_mul` are stated for an arbitrary finite
  group, so the sandwich itself needs no inversion-extension restatement;
* `Lyons.bpAlpha`, `Lyons.bpBeta`, `Lyons.bpGamma`, `Lyons.bpDelta`,
  `Lyons.bp_nonneg`, `Lyons.bp_rel_diag`, `Lyons.bp_rel_off` and
  `Lyons.scalar_ineq` are real arithmetic, with no group in sight;
* `Lyons.blockM`, `Lyons.blockS` and `Lyons.blockM_cfc_rpow`, together with
  `Lyons.spectrum_subset_pair_of_mul_eq_zero`, are statements about a `2 × 2`
  complex matrix;
* `Lyons.algHom_eq_cfc_of_L` is stated for an arbitrary representation of an
  arbitrary finite group's algebra, and `Lyons.exists_unit_phase` is a fact about
  one complex number.

`Lyons.Dihedral.SandwichBlock` is imported for the last of those, which is
why a dihedral module appears in the import list of an inversion-extension one;
the declarations it also brings into scope are shadowed by the
`Lyons.InvExtBlock` ones of the same name.

## Main results

* `Lyons.InvExtBlock.rhoAlg_powElt` : `ρ_{χ,d}` commutes with fractional powers.
* `Lyons.InvExtBlock.rhoAlg_sandwich`,
  `Lyons.InvExtBlock.rhoAlg_sandwich_odd` : the two block forms of the sandwich,
  at an even and at an odd character.
-/

open Finset Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace Lyons.InvExtBlock

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {z : A}
  [hz : Fact (z + z = 0)]

/-! ### `ρ_{χ,d}` commutes with the functional calculus -/

omit [DecidableEq A] in
/-- `ρ_{χ,d}` carries self-adjoint elements to self-adjoint matrices. -/
theorem rhoAlg_isSelfAdjoint (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x) :
    IsSelfAdjoint (rhoAlg χ d x) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← rhoAlg_invol, hsa]

/-- **`ρ_{χ,d}` commutes with fractional powers.**

`powElt x θ` is defined through the functional calculus in the *left regular*
representation, and there is no unital homomorphism from that matrix algebra to
`Matrix (Fin 2) (Fin 2) ℂ` to push `cfc` along; what mediates is the polynomial
interpolation of `Lyons.algHom_eq_cfc_of_L`, which both representations of the
one group algebra transport.

Stated at a character `χ ∈ Â` of a general finite abelian `A` and at an arbitrary
outside index `d`, and with `0 ≤ θ` rather than `θ > 0`, the degenerate exponent
costing nothing. -/
@[lyons_tag "lem_ext_rpow_hom"]
theorem rhoAlg_powElt (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hx : IsPos x) {θ : ℝ} (hθ : 0 ≤ θ) :
    rhoAlg χ d (powElt x θ) = cfc (fun t : ℝ => t ^ θ) (rhoAlg χ d x) := by
  have hle : (0 : Matrix (InvExt A z) (InvExt A z) ℂ) ≤ L x :=
    (isPos_iff_le x).mp hx
  have hL : IsSelfAdjoint (L x) :=
    (Matrix.nonneg_iff_posSemidef.mp hle).isHermitian
  exact algHom_eq_cfc_of_L (rhoAlg χ d) (fun t : ℝ => t ^ θ) hL
    (rhoAlg_isSelfAdjoint χ d x hx.invol_eq) (L_powElt x hx hθ)

/-! ### `ρ_{χ,d}(x)` as a two-by-two block -/

omit [DecidableEq A] in
/-- **`ρ_{χ,d}(x)` is a block of the shape `Lyons.blockM`.** For self-adjoint
`x` the two diagonal entries are the same real number and the two off-diagonal
entries are conjugate, by `rhoAlg_block`. -/
theorem rhoAlg_eq_blockM (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x) {U w : ℝ} {ζ : ℂ}
    (hU : ((U : ℝ) : ℂ) = Ublock x χ) (hV : Vblock x d χ = ζ * (w : ℂ)) :
    rhoAlg χ d x = blockM U w ζ := by
  classical
  rw [rhoAlg_block χ d x hsa, ← hU, hV, blockM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]

omit [DecidableEq A] in
/-- The image of the distinguished outside element `ι d * τ`, as an element of
the group algebra rather than of the group. -/
theorem rhoAlg_single_refl (χ : AddChar A ℂ) (d : A) :
    rhoAlg χ d (MonoidAlgebra.single (InvExt.refl d : InvExt A z) (1 : ℝ))
      = Bchi χ z := by
  rw [rhoAlg_single, one_smul, rho_refl_self]

/-! ### The two block forms of the sandwich -/

/-- **Block form of the sandwich at an even character.**

The displayed matrix is the one of the dihedral computation; the hypothesis
`χ z = 1` is what makes `Bchi χ z` the swap that the dihedral case has for free.

As in the cyclic case, the choice of `ζ` from `V^{x,d}(χ)` and of
`w = |V^{x,d}(χ)|` is left to the caller: any unit `ζ` and any `w ≥ 0` with
`V^{x,d}(χ) = ζ w` will do, and `w ≤ U` is not needed because
`Lyons.blockM_cfc_rpow` does not need it. -/
@[lyons_tag "lem_sandwich_block"]
theorem rhoAlg_sandwich (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hpos : IsPos x) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ' : θ ≤ 1) (hχ : χ z = 1) {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 ≤ w)
    (hU : ((U : ℝ) : ℂ) = Ublock x χ) (hV : Vblock x d χ = ζ * (w : ℂ)) :
    rhoAlg χ d (sandwich x (InvExt.refl d) θ)
      = !![ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ)
              + conj ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ),
           ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
              + ζ ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ);
           ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
              + (conj ζ) ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ),
           ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ)
              + conj ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ)] := by
  have hM : rhoAlg χ d x = blockM U w ζ :=
    rhoAlg_eq_blockM χ d x hpos.invol_eq hU hV
  have hb : rhoAlg χ d (MonoidAlgebra.single (InvExt.refl d : InvExt A z) (1 : ℝ))
      = !![0, 1; 1, 0] := by
    rw [rhoAlg_single_refl, Bchi, hχ]
  rw [sandwich_eq_mul x hpos _ hθ hθ', map_mul, map_mul, hb,
    rhoAlg_powElt χ d x hpos hθ,
    rhoAlg_powElt χ d x hpos (by linarith : (0 : ℝ) ≤ 1 - θ), hM,
    blockM_cfc_rpow hζ hw, blockM_cfc_rpow hζ hw,
    bpAlpha_one_sub, bpBeta_one_sub]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring

/-- **Block form of the sandwich at an odd character.** This is the branch with
no dihedral analogue, and it is the mathematical content of the
generalisation.

At a character with `χ z = -1` the outside transform of a self-adjoint element
vanishes (`Vblock_eq_zero`), so `ρ_{χ,d}(x)` is the scalar `U^x(χ)`. Its
`θ`-th and `(1-θ)`-th powers are the scalars `U^θ` and `U^{1-θ}`, whose product
is `U` because `U ≥ 0`; and `Bchi χ z` is the quarter-turn `!![0, -1; 1, 0]`
rather than a reflection. So the sandwich is `U` times that rotation, and in
particular its upper-left entry — the source's `Q_χ` — is `0`. -/
@[lyons_tag "lem_sandwich_block_odd"]
theorem rhoAlg_sandwich_odd (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hpos : IsPos x) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ' : θ ≤ 1) (hχ : χ z = -1) :
    rhoAlg χ d (sandwich x (InvExt.refl d) θ)
      = !![0, -Ublock x χ; Ublock x χ, 0] := by
  set U : ℝ := (Ublock x χ).re with hUdef
  have hsa : invol x = x := hpos.invol_eq
  have hU : ((U : ℝ) : ℂ) = Ublock x χ := Ublock_ofReal_re x hsa χ
  have hUnn : (0 : ℝ) ≤ U :=
    le_trans (norm_nonneg _) (Ublock_ge_norm_Vblock χ d x hpos hsa)
  have hM : rhoAlg χ d x = blockM U 0 1 :=
    rhoAlg_eq_blockM χ d x hsa hU (by rw [Vblock_eq_zero x hsa d χ hχ]; simp)
  -- The block is scalar, so every fractional power of it is scalar.
  have hpow : ∀ s : ℝ, cfc (fun t : ℝ => t ^ s) (rhoAlg χ d x)
      = ((U ^ s : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro s
    have hα : bpAlpha U 0 s = U ^ s := by unfold bpAlpha; rw [add_zero, sub_zero]; ring
    have hβ : bpBeta U 0 s = 0 := by unfold bpBeta; rw [add_zero, sub_zero]; ring
    rw [hM, blockM_cfc_rpow norm_one le_rfl, hα, hβ]
    simp
  have hb : rhoAlg χ d (MonoidAlgebra.single (InvExt.refl d : InvExt A z) (1 : ℝ))
      = !![0, -1; 1, 0] := by
    rw [rhoAlg_single_refl, Bchi, hχ]
  rw [sandwich_eq_mul x hpos _ hθ hθ', map_mul, map_mul, hb,
    rhoAlg_powElt χ d x hpos hθ,
    rhoAlg_powElt χ d x hpos (by linarith : (0 : ℝ) ≤ 1 - θ), hpow, hpow,
    Matrix.smul_mul, one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    ← Complex.ofReal_mul, mul_comm (U ^ (1 - θ)), rpow_theta_mul hUnn, ← hU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ### Reading the two transforms off the block

`rhoAlg_entries` puts `U^y(χ)` in the upper left and `χ z · V^{y,d}(χ)` in the
upper right, for an arbitrary `y` — which is what the sandwich needs, since the
sandwich is not self-adjoint. The sign `χ z` on the upper-right entry is carried
through the two branches below rather than cancelled: at `χ z = -1` it is exactly
what turns the block's `-U^x(χ)` into `V^{y,d}(χ) = U^x(χ)`. -/

omit [DecidableEq A] in
/-- The abelian transform is the upper-left entry of the block. -/
theorem Ublock_eq_entry (χ : AddChar A ℂ) (d : A)
    (y : MonoidAlgebra ℝ (InvExt A z)) : Ublock y χ = rhoAlg χ d y 0 0 := by
  classical
  rw [rhoAlg_entries]
  simp

omit [DecidableEq A] in
/-- The outside transform, twisted by `χ z`, is the upper-right entry. -/
theorem char_mul_Vblock_eq_entry (χ : AddChar A ℂ) (d : A)
    (y : MonoidAlgebra ℝ (InvExt A z)) :
    χ z * Vblock y d χ = rhoAlg χ d y 0 1 := by
  classical
  rw [rhoAlg_entries]
  simp

section Transforms

variable (χ : AddChar A ℂ) (d : A) (x : MonoidAlgebra ℝ (InvExt A z))
  (hpos : IsPos x) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)

-- Every statement here is about `sandwich x (InvExt.refl d) θ`, whose
-- *definition* already fixes `x` and `θ`, so the three hypotheses appear only
-- inside the proofs and Lean will not include them on its own.
include hpos hθ hθ'

/-- The abelian transform of the sandwich at an even character. -/
theorem Ublock_sandwich (hχ : χ z = 1) {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hw : 0 ≤ w) (hU : ((U : ℝ) : ℂ) = Ublock x χ)
    (hV : Vblock x d χ = ζ * (w : ℂ)) :
    Ublock (sandwich x (InvExt.refl d) θ) χ
      = ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ)
        + conj ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ) := by
  rw [Ublock_eq_entry χ d, rhoAlg_sandwich χ d x hpos hθ hθ' hχ hζ hw hU hV]
  simp

/-- The outside transform of the sandwich at an even character. The `χ z` of
`char_mul_Vblock_eq_entry` is `1` here, so the entry *is* the transform. -/
theorem Vblock_sandwich (hχ : χ z = 1) {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hw : 0 ≤ w) (hU : ((U : ℝ) : ℂ) = Ublock x χ)
    (hV : Vblock x d χ = ζ * (w : ℂ)) :
    Vblock (sandwich x (InvExt.refl d) θ) d χ
      = ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
        + ζ ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ) := by
  have h := char_mul_Vblock_eq_entry χ d (sandwich x (InvExt.refl d) θ)
  rw [rhoAlg_sandwich χ d x hpos hθ hθ' hχ hζ hw hU hV, hχ, one_mul] at h
  rw [h]
  simp

/-- **The abelian transform of the sandwich vanishes at an odd character.** The
source's `Q_χ = 0`. -/
theorem Ublock_sandwich_odd (hχ : χ z = -1) :
    Ublock (sandwich x (InvExt.refl d) θ) χ = 0 := by
  rw [Ublock_eq_entry χ d, rhoAlg_sandwich_odd χ d x hpos hθ hθ' hχ]
  simp

/-- **The outside transform of the sandwich saturates the bound at an odd
character.** The source's `Y_χ = U_χ`: the block is `U^x(χ)` times a quarter
turn, whose upper-right entry is `-U^x(χ)`, and `χ z = -1` cancels the sign. -/
theorem Vblock_sandwich_odd (hχ : χ z = -1) :
    Vblock (sandwich x (InvExt.refl d) θ) d χ = Ublock x χ := by
  have h := char_mul_Vblock_eq_entry χ d (sandwich x (InvExt.refl d) θ)
  rw [rhoAlg_sandwich_odd χ d x hpos hθ hθ' hχ, hχ] at h
  simpa using h

/-- **The sandwich preserves the real part of the outside transform.**

On the even branch both entries carry the same real factor `αδ + βγ`, which is
`w` by the off-diagonal relation, and `ζ` and `conj ζ` have the same real part —
so the expression collapses to `Re(ζ w) = Re V^{x,d}(χ)`. On the odd branch both
sides are `0`, the left by `Ublock_sandwich_odd` and the right by
`Vblock_eq_zero`. -/
@[lyons_tag "lem_Re_Q_eq_Re_V"]
theorem re_Ublock_sandwich :
    (Ublock (sandwich x (InvExt.refl d) θ) χ).re = (Vblock x d χ).re := by
  have hsa : invol x = x := hpos.invol_eq
  rcases char_involution χ hz.out with hχ | hχ
  · obtain ⟨ζ, hζ, hVz⟩ := exists_unit_phase (Vblock x d χ)
    have hU : (((Ublock x χ).re : ℝ) : ℂ) = Ublock x χ := Ublock_ofReal_re x hsa χ
    have hw : (0 : ℝ) ≤ ‖Vblock x d χ‖ := norm_nonneg _
    have hwU : ‖Vblock x d χ‖ ≤ (Ublock x χ).re :=
      Ublock_ge_norm_Vblock χ d x hpos hsa
    have hoff : bpAlpha (Ublock x χ).re ‖Vblock x d χ‖ θ *
          bpDelta (Ublock x χ).re ‖Vblock x d χ‖ θ +
        bpBeta (Ublock x χ).re ‖Vblock x d χ‖ θ *
          bpGamma (Ublock x χ).re ‖Vblock x d χ‖ θ = ‖Vblock x d χ‖ :=
      bp_rel_off hw hwU
    rw [Ublock_sandwich χ d x hpos hθ hθ' hχ hζ hw hU hVz]
    conv_rhs => rw [hVz]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, mul_zero, sub_zero]
    -- Not `rw [← hoff]`: `‖Vblock x d χ‖` also occurs as the *second argument* of
    -- each `bp*`, so rewriting it backwards would substitute inside the very
    -- coefficients being summed.
    linear_combination ζ.re * hoff
  · rw [Ublock_sandwich_odd χ d x hpos hθ hθ' hχ, Vblock_eq_zero x hsa d χ hχ]

/-- **The sandwich transform is dominated.**

On the even branch the upper-right entry is `αγ + ζ²βδ`; the triangle inequality
drops the unit `ζ²` and the diagonal relation identifies `αγ + βδ` with
`U^x(χ)`. On the odd branch the transform *equals* `U^x(χ)`, which is a
nonnegative real, so the inequality holds with equality. -/
@[lyons_tag "lem_absY_le_U"]
theorem norm_Vblock_sandwich_le :
    ‖Vblock (sandwich x (InvExt.refl d) θ) d χ‖ ≤ (Ublock x χ).re := by
  have hsa : invol x = x := hpos.invol_eq
  have hnn : (0 : ℝ) ≤ (Ublock x χ).re :=
    le_trans (norm_nonneg _) (Ublock_ge_norm_Vblock χ d x hpos hsa)
  rcases char_involution χ hz.out with hχ | hχ
  · obtain ⟨ζ, hζ, hVz⟩ := exists_unit_phase (Vblock x d χ)
    have hU : (((Ublock x χ).re : ℝ) : ℂ) = Ublock x χ := Ublock_ofReal_re x hsa χ
    have hw : (0 : ℝ) ≤ ‖Vblock x d χ‖ := norm_nonneg _
    have hwU : ‖Vblock x d χ‖ ≤ (Ublock x χ).re :=
      Ublock_ge_norm_Vblock χ d x hpos hsa
    obtain ⟨hα, hβ, hγ, hδ⟩ := bp_nonneg hw hwU hθ hθ'
    rw [Vblock_sandwich χ d x hpos hθ hθ' hχ hζ hw hU hVz]
    calc ‖((bpAlpha (Ublock x χ).re ‖Vblock x d χ‖ θ *
                bpGamma (Ublock x χ).re ‖Vblock x d χ‖ θ : ℝ) : ℂ)
            + ζ ^ 2 * ((bpBeta (Ublock x χ).re ‖Vblock x d χ‖ θ *
                bpDelta (Ublock x χ).re ‖Vblock x d χ‖ θ : ℝ) : ℂ)‖
        ≤ _ + _ := norm_add_le _ _
      _ = bpAlpha (Ublock x χ).re ‖Vblock x d χ‖ θ *
              bpGamma (Ublock x χ).re ‖Vblock x d χ‖ θ +
            bpBeta (Ublock x χ).re ‖Vblock x d χ‖ θ *
              bpDelta (Ublock x χ).re ‖Vblock x d χ‖ θ := by
          rw [norm_mul, norm_pow, hζ, one_pow, one_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hα hγ),
            Real.norm_of_nonneg (mul_nonneg hβ hδ)]
      _ = (Ublock x χ).re := bp_rel_diag hw hwU
  · rw [Vblock_sandwich_odd χ d x hpos hθ hθ' hχ]
    have hnorm : ‖Ublock x χ‖ = (Ublock x χ).re := by
      conv_lhs => rw [← Ublock_ofReal_re x hsa χ]
      rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    exact hnorm.le

end Transforms

/-! ### Consequences for the coefficient functions

The two statements above concern the *transforms*; these pull them back to the
coefficient functions, which is the form the reflection inequality needs. -/

omit [DecidableEq A] hz in
/-- Splitting a sum over `G_{A,z}` along the normal form **at a chosen `d`**: the
outside half is reindexed by `a ↦ a + d`, so that its summand is the coefficient
at `ι (a d) τ`. This is the index-set half of `Lyons.sum_coeff_split`: the raw
bijection, without a summand `Ψ`. -/
theorem sum_invExt_shift {M : Type*} [AddCommMonoid M] (d : A)
    (F : InvExt A z → M) :
    ∑ g : InvExt A z, F g
      = (∑ a : A, F (.rot a)) + ∑ a : A, F (.refl (a + d)) := by
  rw [sum_invExt F]
  congr 1
  exact sum_shift d fun a => F (InvExt.refl a)

section Coefficients

variable (d : A) (x : MonoidAlgebra ℝ (InvExt A z)) (hpos : IsPos x) {θ : ℝ}
  (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)

include hpos hθ hθ'

/-- **The sandwich preserves the even part of the abelian coefficients.**

Equal real parts of the transforms force equal even parts, by injectivity of the
transform — `AddCharFourier.evenPart_eq_of_re_dft_eq`. -/
@[lyons_tag "lem_sandwich_even_part"]
theorem evenPart_uCoeff_sandwich :
    AddCharFourier.evenPart (uCoeff (sandwich x (InvExt.refl d) θ))
      = AddCharFourier.evenPart (vCoeff x d) :=
  AddCharFourier.evenPart_eq_of_re_dft_eq (conj_uCoeff _) (conj_vCoeff _ _)
    fun χ => re_Ublock_sandwich χ d x hpos hθ hθ'

/-- **Pairing against a power of the abelian coefficients is unchanged by the
sandwich.**

Stated for an arbitrary natural exponent `p` rather than the source's `2m - 1`:
the proof needs only that `u^x` is even, hence that any power of it is, and
dropping the restriction keeps the natural subtraction `2 * m - 1` out of the
statement. -/
@[lyons_tag "lem_sandwich_pairing"]
theorem sum_uCoeff_pow_mul_sandwich (p : ℕ) :
    ∑ a : A, uCoeff x a ^ p * uCoeff (sandwich x (InvExt.refl d) θ) a
      = ∑ a : A, uCoeff x a ^ p * vCoeff x d a := by
  have heven : ∀ a : A, uCoeff x (-a) ^ p = uCoeff x a ^ p := fun a => by
    rw [uCoeff_neg x hpos.invol_eq a]
  rw [AddCharFourier.sum_mul_evenPart (fun a => uCoeff x a ^ p) _ heven,
    AddCharFourier.sum_mul_evenPart (fun a => uCoeff x a ^ p) (vCoeff x d) heven,
    evenPart_uCoeff_sandwich d x hpos hθ hθ']

/-- **Norm domination for the sandwich.**

`U^x` is a nonnegative real dominating `|V^{y,d}|` pointwise on the dual, which
is exactly the hypothesis of the majorant inequality
`AddCharFourier.sum_pow_le_of_dft_le`. -/
@[lyons_tag "lem_sandwich_norm"]
theorem sum_norm_vCoeff_sandwich_le {m : ℕ} (hm : 1 ≤ m) :
    ∑ a : A, ‖vCoeff (sandwich x (InvExt.refl d) θ) d a‖ ^ (2 * m)
      ≤ ∑ a : A, ‖uCoeff x a‖ ^ (2 * m) := by
  have hsa : invol x = x := hpos.invol_eq
  exact AddCharFourier.sum_pow_le_of_dft_le _ _ m hm
    (fun χ => Ublock_ofReal_re x hsa χ)
    (fun χ => le_trans (norm_nonneg _) (Ublock_ge_norm_Vblock χ d x hpos hsa))
    (fun χ => norm_Vblock_sandwich_le χ d x hpos hθ hθ')

/-! ### The reflection inequality -/

/-- The abelian-half pairing, with real coefficients. `uCoeff` and `vCoeff` are
`ℂ`-valued because they feed the transform; the identity they satisfy is the
coercion of this real one, and coercion is injective. -/
theorem sum_co_pow_mul_sandwich (p : ℕ) :
    ∑ a : A, co x (.rot a) ^ p * co (sandwich x (InvExt.refl d) θ) (.rot a)
      = ∑ a : A, co x (.rot a) ^ p * co x (.refl (a + d)) := by
  have h := sum_uCoeff_pow_mul_sandwich d x hpos hθ hθ' p
  simp only [uCoeff, vCoeff] at h
  exact_mod_cast h

/-- The sandwich's outside coefficients are dominated in counting norm by the
abelian coefficients of `x`. This is `sum_norm_vCoeff_sandwich_le` pulled back
from `‖·‖` on `ℂ` to `|·|` on `ℝ`, and then to the roots. -/
theorem rootSum_co_sandwich_le (p : ℕ) :
    rootSum univ
        (fun a : A => |co (sandwich x (InvExt.refl d) θ) (.refl (a + d))|) (2 * p)
      ≤ rootSum univ (fun a : A => |co x (.rot a)|) (2 * p) := by
  refine rootSum_le_rootSum (fun a _ => abs_nonneg _) ?_
  have h := sum_norm_vCoeff_sandwich_le d x hpos hθ hθ' (m := p + 1)
    (Nat.le_add_left 1 p)
  simpa [vCoeff, uCoeff, Nat.mul_succ] using h

/-- **The reflection inequality**, the source's Proposition 2.3.

Split both sums along the normal form at `d`. On the abelian half the sandwich is
invisible (`sum_co_pow_mul_sandwich`), so that term becomes an
abelian-against-outside pairing; Hölder bounds each of the two halves by a
product of counting norms, `rootSum_co_sandwich_le` replaces the sandwich's norm
by `‖u^x‖`, and `Lyons.scalar_ineq` collapses `R^{2m-1}S + RS^{2m-1}` to
`R^{2m} + S^{2m}` — which is the right-hand side reassembled.

Stated with `2 * p + 1` and `2 * p + 2` rather than the source's `2m - 1` and
`2m` (so `m = p + 1`): truncated natural subtraction in an exponent is a
liability in every rewrite that touches it, and the two forms are interchangeable
under the standing hypothesis `m ≥ 1`.

Stated over the inversion extension of a general finite abelian `A` and at an
arbitrary outside element `ι(d)τ`. -/
@[lyons_tag "prop_reflection_inequality"]
theorem sum_co_pow_mul_sandwich_le (p : ℕ) :
    ∑ g : InvExt A z,
        co x g ^ (2 * p + 1) * co (sandwich x (InvExt.refl d) θ) g
      ≤ ∑ g : InvExt A z, co x g ^ (2 * p + 2) := by
  classical
  have hev : Even (2 * p + 2) := ⟨p + 1, by ring⟩
  set R : ℝ := rootSum univ (fun a : A => |co x (.rot a)|) (2 * p) with hR
  set S : ℝ := rootSum univ (fun a : A => |co x (.refl (a + d))|) (2 * p) with hS
  have hR0 : 0 ≤ R := rootSum_nonneg (fun a _ => abs_nonneg _) _
  have hS0 : 0 ≤ S := rootSum_nonneg (fun a _ => abs_nonneg _) _
  -- Each half: pass to absolute values, then Hölder.
  have habs : ∀ f h : A → ℝ,
      ∑ a : A, f a ^ (2 * p + 1) * h a
        ≤ ∑ a : A, |f a| ^ (2 * p + 1) * |h a| := fun f h =>
    Finset.sum_le_sum fun a _ =>
      (le_abs_self _).trans (by rw [abs_mul, abs_pow])
  have hrot : ∑ a : A, co x (.rot a) ^ (2 * p + 1) * co x (.refl (a + d))
      ≤ R ^ (2 * p + 1) * S :=
    (habs _ _).trans (sum_pow_succ_mul_le (fun a _ => abs_nonneg _)
      (fun a _ => abs_nonneg _) (2 * p))
  have hrefl : ∑ a : A, co x (.refl (a + d)) ^ (2 * p + 1) *
        co (sandwich x (InvExt.refl d) θ) (.refl (a + d))
      ≤ S ^ (2 * p + 1) * R := by
    refine (habs _ _).trans ?_
    refine (sum_pow_succ_mul_le (fun a _ => abs_nonneg _)
      (fun a _ => abs_nonneg _) (2 * p)).trans ?_
    exact mul_le_mul_of_nonneg_left (rootSum_co_sandwich_le d x hpos hθ hθ' p)
      (pow_nonneg hS0 _)
  calc ∑ g : InvExt A z,
          co x g ^ (2 * p + 1) * co (sandwich x (InvExt.refl d) θ) g
      = (∑ a : A, co x (.rot a) ^ (2 * p + 1) *
            co (sandwich x (InvExt.refl d) θ) (.rot a))
          + ∑ a : A, co x (.refl (a + d)) ^ (2 * p + 1) *
            co (sandwich x (InvExt.refl d) θ) (.refl (a + d)) :=
        sum_invExt_shift d _
    _ = (∑ a : A, co x (.rot a) ^ (2 * p + 1) * co x (.refl (a + d)))
          + ∑ a : A, co x (.refl (a + d)) ^ (2 * p + 1) *
            co (sandwich x (InvExt.refl d) θ) (.refl (a + d)) := by
        rw [sum_co_pow_mul_sandwich d x hpos hθ hθ' (2 * p + 1)]
    _ ≤ R ^ (2 * p + 1) * S + S ^ (2 * p + 1) * R := add_le_add hrot hrefl
    _ ≤ R ^ (2 * p + 2) + S ^ (2 * p + 2) := by
        have := scalar_ineq hR0 hS0 (2 * p + 1)
        nlinarith [this]
    _ = ∑ g : InvExt A z, co x g ^ (2 * p + 2) := by
        rw [hR, hS, rootSum_pow (fun a _ => abs_nonneg _),
          rootSum_pow (fun a _ => abs_nonneg _),
          sum_invExt_shift d fun g => co x g ^ (2 * p + 2)]
        congr 1 <;> exact Finset.sum_congr rfl fun a _ => hev.pow_abs _

end Coefficients

end Lyons.InvExtBlock
