/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.GroupAlgebra.Imported
import Lyons.GroupAlgebra.Positivity
import Lyons.Objective.RateMonotonic

/-!
# Realising an element of the group algebra as a centered heat element

This is the step that turns an *algebraic* counterexample into a statement about
random walks: an element `x ⪰ 0` of `ℝ[H]` which annihilates `π_H` and is
positive definite off the constants is exhibited as `e^{-ϱ}` times the time-`1`
centered heat element of an honest generating symmetric rate collection.

## The route

`π_H + x` is positive definite (`Lyons.posDef_L_uniform_add`), so its logarithm
exists; the logarithm is again a left convolution and has real entries, so it is
`L` of a group-algebra element (`Lyons.negLogElt`). Calling that element `Y`, the
Laplacian of the rate collection `λ_s = ϱ/|H| - Y_s` is `Y + ϱ(1 - π_H)`, whose
exponential is `π_H + e^{-ϱ} x`.

## The topology diamond, once

`Lyons.exp_smul_of_isIdempotentElem` is stated in an abstract normed ring, and on
`Matrix n n ℂ` the `NormedRing` instance it needs lives in the scoped
`Matrix.Norms.Operator`, whose topology is *definitionally* but not syntactically
the ambient product topology that `Lyons.heatMat` is computed in. Opening the
scope for the whole file makes `rw` fail on patterns that are visibly present, so
the scope is opened exactly once, inside the proof term of
`Lyons.matrix_exp_smul_of_isIdempotentElem`, whose statement is in the ambient
topology. This is how Mathlib's own `Matrix.exp_add_of_commute` is written.

## Main definitions

* `Lyons.negLogElt` : minus the functional-calculus logarithm of `L z`, read off
  column one.

## Main results

* `Lyons.posDef_L_uniform_add` : `L (π_H + x)` is positive definite.
* `Lyons.exists_invol_eq_exp_neg_L` : a logarithm in the group algebra.
* `Lyons.exists_rate_centeredHeat_eq` : realisation as a centered heat element.
-/

open Matrix
-- `Matrix.PosDef` is an order-theoretic statement about `⟪M η, η⟫ : ℂ`.
open scoped ComplexOrder

namespace Lyons

variable {H : Type*} [Group H] [Fintype H] [DecidableEq H]

/-! ### `π_H + x` is positive definite -/

section PosDef

variable {x : MonoidAlgebra ℝ H}

omit [DecidableEq H] in
/-- `π_H + x` is self-adjoint whenever `x` is. -/
theorem invol_uniform_add (hx : IsPos x) : invol (uniform H + x) = uniform H + x := by
  refine co_injective fun g ↦ ?_
  have hxinv : co x g⁻¹ = co x g := by rw [← co_invol, hx.invol_eq]
  rw [co_invol, co_add, co_add, coe_uniform, coe_uniform, hxinv]

set_option linter.unusedDecidableInType false in
/-- **`L (π_H + x)` is positive definite.**

No splitting of `η` as `Pη + (I - P)η`, and hence no appeal to
`L_x P = P L_x = 0`, is needed: the two cases `Pη ≠ 0` and `Pη = 0` already
exhaust the possibilities, and in the second the hypothesis of
`Lyons.IsPosDefOffConst` is literally available. So `x π_H = 0` is not used
here. -/
theorem posDef_L_uniform_add (hx : IsPos x) (hpd : IsPosDefOffConst x) :
    (L (uniform H + x)).PosDef := by
  have hxps : (L x).PosSemidef := hx
  have hPidem : L (uniform H) * L (uniform H) = L (uniform H) := L_uniform_mul_self
  have hPherm : (L (uniform H) : Matrix H H ℂ)ᴴ = L (uniform H) := L_uniform_conjTranspose
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun η hη ↦ ?_
  · change (L (uniform H + x))ᴴ = L (uniform H + x)
    rw [← L_invol, invol_uniform_add hx]
  rw [L_add, add_mulVec, dotProduct_add]
  by_cases hPη : L (uniform H) *ᵥ η = 0
  · rw [hPη, dotProduct_zero, zero_add]
    exact hpd hη hPη
  · refine add_pos_of_pos_of_nonneg ?_ (hxps.dotProduct_mulVec_nonneg η)
    -- `P` is an orthogonal projection, so its quadratic form is `‖Pη‖²`.
    have hquad : star η ⬝ᵥ (L (uniform H) *ᵥ η)
        = star (L (uniform H) *ᵥ η) ⬝ᵥ (L (uniform H) *ᵥ η) := by
      rw [star_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, hPherm, hPidem]
    rw [hquad]
    exact dotProduct_star_self_pos_iff.mpr hPη

end PosDef

/-! ### The exponential of a real multiple of an idempotent matrix -/

/-- `Lyons.exp_smul_of_isIdempotentElem` at matrices, stated in the ambient
product topology.

The abstract lemma needs a `NormedRing`, which on matrices only exists in the
scoped `Matrix.Norms.Operator`; the scope is opened for the proof term alone, so
that the statement — and hence every `rw` against it below — stays on the same
side of the topology diamond as `Lyons.heatMat`. Mathlib's
`Matrix.exp_add_of_commute` is written the same way. -/
theorem matrix_exp_smul_of_isIdempotentElem {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : IsIdempotentElem Q) (s : ℝ) :
    NormedSpace.exp (s • Q) = 1 + (Real.exp s - 1) • Q :=
  open scoped Norms.Operator in exp_smul_of_isIdempotentElem hQ s

/-! ### The logarithm -/

/-- **Minus the functional-calculus logarithm of `L z`**, read off column one.

The coefficients are `Y_g = -(φ(M))_{g,1}`; the sign is built into the definition
so that no negation of a group-algebra element is needed anywhere below. The
construction is the one
`Lyons.sqrtElt` and `Lyons.powElt` use: the functional calculus of a left
convolution is again a left convolution (`Lyons.cfc_L_conv`) with real entries
(`Lyons.cfc_L_im_eq_zero`), so its first column is the coefficient function of a
genuine element of `ℝ[H]`. -/
noncomputable def negLogElt (z : MonoidAlgebra ℝ H) : MonoidAlgebra ℝ H :=
  ofFun fun g ↦ -(cfc Real.log (L z) g 1).re

/-- The left regular matrix of `Lyons.negLogElt z` is minus the logarithm of
`L z`. -/
theorem L_negLogElt {z : MonoidAlgebra ℝ H} (hz : (L z).PosDef) :
    L (negLogElt z) = -cfc Real.log (L z) := by
  have hsa : IsSelfAdjoint (L z) := hz.isHermitian
  have hcont : ContinuousOn Real.log (spectrum ℝ (L z)) :=
    Real.continuousOn_log.mono fun r hr ↦ (spectrum_pos_of_posDef hz r hr).ne'
  ext g h
  have hreal : (cfc Real.log (L z) (g * h⁻¹) 1).im = 0 :=
    cfc_L_im_eq_zero z Real.log hcont hsa _ _
  have hconv : cfc Real.log (L z) g h = cfc Real.log (L z) (g * h⁻¹) 1 :=
    cfc_L_conv z Real.log g h
  rw [L_apply, negLogElt, co_ofFun, Matrix.neg_apply, hconv]
  apply Complex.ext <;> simp [hreal]

/-- **A logarithm in the group algebra.** A positive element `x` of `ℝ[H]` which
is positive definite off the constants has `π_H + x = e^{-L_Y}` for a
self-adjoint `Y ∈ ℝ[H]`.

No hypothesis `x π_H = 0` is needed; see `Lyons.posDef_L_uniform_add`. The
function fed to the functional calculus is `Real.log` itself rather than an
arbitrary function agreeing with `ln` on the spectrum of `L (π_H + x)`, for which
generality see `Lyons.exp_cfc_eq_of_eqOn_log`. -/
@[lyons_tag "lem_log_element"]
theorem exists_invol_eq_exp_neg_L {x : MonoidAlgebra ℝ H} (hx : IsPos x)
    (hpd : IsPosDefOffConst x) :
    ∃ Y : MonoidAlgebra ℝ H, invol Y = Y ∧
      NormedSpace.exp (-(L Y)) = L (uniform H + x) := by
  have hz : (L (uniform H + x)).PosDef := posDef_L_uniform_add hx hpd
  refine ⟨negLogElt (uniform H + x), L_injective ?_, ?_⟩
  · rw [L_invol, L_negLogElt hz, Matrix.conjTranspose_neg]
    exact congrArg Neg.neg (cfc_isHermitian Real.log (L (uniform H + x)))
  · rw [L_negLogElt hz, neg_neg]
    exact exp_cfc_eq_of_eqOn_log hz fun _ _ ↦ rfl

/-! ### Realisation as a centered heat element -/

/-- **Realisation as a centered heat element.** A positive element `x` of `ℝ[H]`
which annihilates `π_H` and is positive definite off the constants is `e^{-ϱ}`
times the time-`1` centered heat element of a generating symmetric rate
collection that is strictly positive off the identity.

The word *generating* is load-bearing: `Lyons.RateMonotonic` quantifies only over
generating collections, so a realisation achieving only symmetry would refute
nothing. Strict positivity at every non-identity element is what supplies it, and
it is stated as well as used because the consumer needs a strictly positive rate
at one named element in order to differentiate in it.

Bookkeeping conventions:

* `ϱ` is taken to be `|H| (1 + ∑_g |Y_g|)` rather than an arbitrary number
  exceeding `|H| (1 + max_g |Y_g|)`; a sum avoids `Finset.max'` and its
  nonemptiness side condition, and dominates each `|Y_g|` just as well.
* The rate collection is an `Lyons.IsSymmRate` on all of `H`, with value `0` at
  the identity, and `λ°` is `Lyons.IsSymmRate.toRateFn`, following
  `Lyons.Walk.Basic`'s convention that rates are total functions.
* The conclusion is stated with `Lyons.centeredHeatCoeffReal`, the `ℝ`-valued
  coefficient function of `a_1^{λ°}`, and with `Lyons.co` for the coefficients of
  `x`. -/
@[lyons_tag "lem_heat_realization"]
theorem exists_rate_centeredHeat_eq {x : MonoidAlgebra ℝ H} (hx : IsPos x)
    (hxu : x * uniform H = 0) (hpd : IsPosDefOffConst x) :
    ∃ (lam : H → ℝ) (hlam : IsSymmRate lam) (rho : ℝ),
      Generating lam ∧ (∀ s : H, s ≠ 1 → 0 < lam s) ∧ 0 < rho ∧
        ∀ g : H, centeredHeatCoeffReal hlam.toRateFn 1 g = Real.exp (-rho) * co x g := by
  classical
  obtain ⟨Y, hYinv, hYexp⟩ := exists_invol_eq_exp_neg_L hx hpd
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard' : (Fintype.card H : ℝ) ≠ 0 := ne_of_gt hcard
  have hPidem : L (uniform H) * L (uniform H) = L (uniform H) := L_uniform_mul_self
  have hPidem' : IsIdempotentElem (L (uniform H) : Matrix H H ℂ) := hPidem
  have hxP : L x * L (uniform H) = 0 := by rw [← L_mul, hxu, L_zero]
  -- Step 1: the coefficients of `Y` sum to zero.
  have hsig : ∑ g : H, co Y g = 0 := by
    set σ : ℝ := ∑ g : H, co Y g with hσ
    have hYP : L Y * L (uniform H) = σ • L (uniform H) := by
      rw [← L_mul, uniform_absorb, L_smul]
    have hPY : L (uniform H) * L Y = σ • L (uniform H) := by
      rw [← L_mul, uniform_mul_absorb, L_smul]
    -- `Z` is the part of `L Y` transverse to `P`.
    set Z : Matrix H H ℂ := L Y - σ • L (uniform H) with hZ
    have hZP : (-Z) * L (uniform H) = 0 := by
      rw [hZ, neg_sub, sub_mul, smul_mul_assoc, hPidem, hYP, sub_self]
    have hPZ : L (uniform H) * (-Z) = 0 := by
      rw [hZ, neg_sub, mul_sub, mul_smul_comm, hPidem, hPY, sub_self]
    have hdecomp : -(L Y) = -Z + (-σ) • L (uniform H) := by
      rw [hZ, neg_smul]
      abel
    have hcomm : (-Z) * ((-σ) • L (uniform H)) = ((-σ) • L (uniform H)) * (-Z) := by
      rw [mul_smul_comm, hZP, smul_mul_assoc, hPZ]
    have hexpZ : NormedSpace.exp (-Z) * L (uniform H) = L (uniform H) :=
      exp_mul_of_mul_eq_zero hZP
    have hcollapse : ((1 : Matrix H H ℂ)
          + (Real.exp (-σ) - 1) • (L (uniform H) : Matrix H H ℂ)) * L (uniform H)
        = Real.exp (-σ) • (L (uniform H) : Matrix H H ℂ) := by
      rw [add_mul, one_mul, smul_mul_assoc, hPidem, sub_smul, one_smul]
      abel
    have hkey : Real.exp (-σ) • (L (uniform H) : Matrix H H ℂ) = L (uniform H) := by
      have hlhs : NormedSpace.exp (-(L Y)) * L (uniform H)
          = Real.exp (-σ) • (L (uniform H) : Matrix H H ℂ) := by
        rw [hdecomp, exp_add_of_mul_comm hcomm,
          matrix_exp_smul_of_isIdempotentElem hPidem' (-σ), mul_assoc, hcollapse,
          mul_smul_comm, hexpZ]
      rw [← hlhs, hYexp, L_add, add_mul, hPidem, hxP, add_zero]
    -- Read off the `(1, 1)` entry.
    have hentry := congrFun (congrFun hkey 1) 1
    rw [Matrix.smul_apply, L_apply, inv_one, mul_one, coe_uniform,
      Complex.real_smul] at hentry
    have hreal : Real.exp (-σ) * ((Fintype.card H : ℝ))⁻¹ = ((Fintype.card H : ℝ))⁻¹ := by
      exact_mod_cast hentry
    have hone : Real.exp (-σ) = 1 :=
      mul_right_cancel₀ (inv_ne_zero hcard') (by rw [one_mul]; exact hreal)
    have hzero : -σ = 0 := by rw [← Real.log_exp (-σ), hone, Real.log_one]
    linarith
  -- `Y` now annihilates `π_H` on both sides.
  have hYP0 : L Y * L (uniform H) = 0 := by
    rw [← L_mul, uniform_absorb, hsig, zero_smul, L_zero]
  have hPY0 : L (uniform H) * L Y = 0 := by
    rw [← L_mul, uniform_mul_absorb, hsig, zero_smul, L_zero]
  -- Step 2: the rate collection.
  set rho : ℝ := (Fintype.card H : ℝ) * (1 + ∑ g : H, |co Y g|) with hrhodef
  have hsumabs : 0 ≤ ∑ g : H, |co Y g| := Finset.sum_nonneg fun g _ ↦ abs_nonneg _
  have hrho : 0 < rho := by
    rw [hrhodef]
    exact mul_pos hcard (by linarith)
  have hrhodiv : rho / (Fintype.card H : ℝ) = 1 + ∑ g : H, |co Y g| := by
    rw [hrhodef]
    field_simp
  have hlt : ∀ g : H, co Y g < rho / (Fintype.card H : ℝ) := by
    intro g
    rw [hrhodiv]
    have h1 : co Y g ≤ |co Y g| := le_abs_self _
    have h2 : |co Y g| ≤ ∑ h : H, |co Y h| :=
      Finset.single_le_sum (fun h _ ↦ abs_nonneg (co Y h)) (Finset.mem_univ g)
    linarith
  set lam : H → ℝ := fun g ↦ if g = 1 then 0 else rho / (Fintype.card H : ℝ) - co Y g
    with hlamdef
  have hlampos : ∀ s : H, s ≠ 1 → 0 < lam s := by
    intro s hs
    rw [hlamdef]
    simp only [if_neg hs]
    linarith [hlt s]
  have hlamS : IsSymmRate lam := by
    refine ⟨fun g ↦ ?_, fun g ↦ ?_⟩
    · by_cases hg : g = 1
      · simp [hlamdef, hg]
      · exact (hlampos g hg).le
    · by_cases hg : g = 1
      · simp [hlamdef, hg]
      · have hg' : g⁻¹ ≠ 1 := by simpa using hg
        have hYcoe : co Y g⁻¹ = co Y g := by rw [← co_invol, hYinv]
        simp only [hlamdef, if_neg hg, if_neg hg', hYcoe]
  refine ⟨lam, hlamS, rho, ?_, hlampos, hrho, ?_⟩
  · -- generating: the support is all of `H \ {1}`, which generates `H`
    refine (Subgroup.eq_top_iff' _).2 fun g ↦ ?_
    by_cases hg : g = 1
    · rw [hg]; exact one_mem _
    · exact Subgroup.subset_closure (hlampos g hg)
  -- Step 3: the Laplacian.
  have hnu : ∀ g : H, (hlamS.toRateFn : H → ℝ) g
      = if g = 1 then 0 else rho / (Fintype.card H : ℝ) - co Y g := by
    intro g
    rw [IsSymmRate.toRateFn_apply]
    by_cases hg : g = 1 <;> simp [hg, hlamdef]
  have hsum : ∑ s : H, (hlamS.toRateFn : H → ℝ) s
      = rho - (rho / (Fintype.card H : ℝ) - co Y 1) := by
    have hf : ∀ s : H, (hlamS.toRateFn : H → ℝ) s
        = (rho / (Fintype.card H : ℝ) - co Y s)
          - (if s = 1 then rho / (Fintype.card H : ℝ) - co Y 1 else 0) := by
      intro s
      rw [hnu]
      by_cases hs : s = 1 <;> simp [hs]
    rw [Finset.sum_congr rfl fun s _ ↦ hf s, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ (1 : H)
        (fun _ ↦ rho / (Fintype.card H : ℝ) - co Y 1)]
    simp only [Finset.mem_univ, if_true]
    congr 1
    rw [Finset.sum_sub_distrib, hsig, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      sub_zero]
    field_simp
  have hlap : laplacian hlamS.toRateFn = Y + rho • (1 - uniform H) := by
    refine co_injective fun g ↦ ?_
    rw [coe_laplacian, hsum, hnu, co_add, co_smul, co_sub, co_one, coe_uniform]
    by_cases hg : g = 1
    · simp only [hg, if_true]
      field_simp
      ring
    · simp only [if_neg hg]
      field_simp
      ring
  -- Step 4: the heat matrix at time one.
  have hQidem : IsIdempotentElem (1 - L (uniform H) : Matrix H H ℂ) := by
    rw [IsIdempotentElem, sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hPidem]
    abel
  have hQY : L Y * (1 - L (uniform H) : Matrix H H ℂ) = L Y := by
    rw [mul_sub, mul_one, hYP0, sub_zero]
  have hYQ : (1 - L (uniform H) : Matrix H H ℂ) * L Y = L Y := by
    rw [sub_mul, one_mul, hPY0, sub_zero]
  have hcomm : (-(L Y)) * ((-rho) • (1 - L (uniform H) : Matrix H H ℂ))
      = ((-rho) • (1 - L (uniform H) : Matrix H H ℂ)) * (-(L Y)) := by
    rw [mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg, hQY, hYQ]
  have hexpo : -((1 : ℝ) : ℂ) • L (laplacian hlamS.toRateFn)
      = -(L Y) + (-rho) • (1 - L (uniform H) : Matrix H H ℂ) := by
    rw [hlap, L_add, L_smul, L_sub, L_one, Complex.ofReal_one, neg_one_smul, neg_add,
      ← neg_smul]
  have hPQ : L (uniform H) * (1 - L (uniform H) : Matrix H H ℂ) = 0 := by
    rw [mul_sub, mul_one, hPidem, sub_self]
  have hxQ : L x * (1 - L (uniform H) : Matrix H H ℂ) = L x := by
    rw [mul_sub, mul_one, hxP, sub_zero]
  have hfinal : heatMat hlamS.toRateFn 1 = L (uniform H + Real.exp (-rho) • x) := by
    rw [heatMat, hexpo, exp_add_of_mul_comm hcomm, hYexp,
      matrix_exp_smul_of_isIdempotentElem hQidem (-rho), L_add, L_add, L_smul, mul_add,
      mul_one, mul_smul_comm, add_mul, hPQ, hxQ, zero_add, sub_smul, one_smul]
    abel
  -- Step 5: the conclusion.
  intro g
  rw [centeredHeatCoeffReal, heatCoeffReal, heatCoeff, hfinal, L_apply, inv_one, mul_one,
    Complex.ofReal_re, co_add, co_smul, coe_uniform]
  ring

end Lyons
