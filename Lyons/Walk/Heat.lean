/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Laplacian

/-!
# The heat element, and absorption of the uniform element

`Lyons.heatMat` is a matrix and `Lyons.heatCoeff` its first column. Everything
from here on treats the heat semigroup *algebraically* — multiplying it by the
uniform element, taking fractional powers, feeding it to a second representation
— and none of that can be done to a column. So this file reconstructs the
group-algebra element, exactly as `Lyons.powElt` did for fractional powers.

## The one analytic input

`Lyons.exp_mul_of_mul_eq_zero`: if `A * B = 0` then `exp A * B = B`. This is the
whole content of absorption. Going through `Δ_λ π_G = 0` uses the exponential
series exactly once, in one reusable lemma, and the coefficient sum then
*follows* from absorption. The alternative route, deriving absorption from the
coefficient sum being `1` via the augmentation `x ↦ ∑ x_g` being an algebra
homomorphism, needs the series pushed through the augmentation anyway, and the
augmentation is not available on the matrix side where the exponential lives.

## Main definitions

* `Lyons.heatElt` : `h_t^λ`, the heat element of the group algebra.

## Main results

* `Lyons.exp_mul_of_mul_eq_zero` : the exponential fixes what the generator kills.
* `Lyons.L_heatElt` : its left regular matrix is `heatMat`.
* `Lyons.heatElt_absorb` : `h_t^λ π_G = π_G h_t^λ = π_G`.
* `Lyons.sum_heatCoeffReal` : `∑ g, p_t^λ(g) = 1`.
-/

open Matrix
-- Needed for the `NormedRing` instance that `NormedSpace.exp`'s lemmas require;
-- Mathlib's own matrix-exponential lemmas open exactly this scope.
open scoped Norms.Operator

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### The exponential fixes what the generator annihilates -/

omit [Group G] in
/-- **If `A` annihilates `B` on the right, so does every positive power, and the
exponential therefore fixes `B`.**

This replaces every appeal to "the exponential series converges coefficientwise":
the series is summable, right multiplication is continuous, and every term past
the zeroth vanishes. -/
theorem exp_mul_of_mul_eq_zero {A B : Matrix G G ℂ} (h : A * B = 0) :
    NormedSpace.exp A * B = B := by
  have hs : Summable fun n : ℕ => ((Nat.factorial n : ℚ)⁻¹) • A ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℚ) A
  rw [NormedSpace.exp_eq_tsum_rat, ← hs.tsum_mul_right, tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [smul_mul_assoc, pow_succ, mul_assoc, h, mul_zero, smul_zero]

omit [Group G] in
/-- The left-hand version. -/
theorem mul_exp_of_mul_eq_zero {A B : Matrix G G ℂ} (h : B * A = 0) :
    B * NormedSpace.exp A = B := by
  have hs : Summable fun n : ℕ => ((Nat.factorial n : ℚ)⁻¹) • A ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℚ) A
  rw [NormedSpace.exp_eq_tsum_rat, ← hs.tsum_mul_left, tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [mul_smul_comm, pow_succ', ← mul_assoc, h, zero_mul, smul_zero]

/-! ### The uniform element on the left -/

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- Coefficients of `π_G * x`, the mirror of `Lyons.coe_mul_uniform`. -/
theorem coe_uniform_mul (x : MonoidAlgebra ℝ G) (g : G) :
    co (uniform G * x) g = (∑ h : G, co x h) * (Fintype.card G : ℝ)⁻¹ := by
  classical
  rw [co_mul]
  simp only [coe_uniform]
  rw [← Finset.mul_sum, mul_comm]

set_option linter.unusedDecidableInType false in
/-- **Absorption on the left.** -/
theorem uniform_mul_absorb (x : MonoidAlgebra ℝ G) :
    uniform G * x = (∑ h : G, co x h) • uniform G := by
  refine co_injective fun g ↦ ?_
  rw [coe_uniform_mul, co_smul, coe_uniform]

set_option linter.unusedDecidableInType false in
/-- The Laplacian has coefficient sum zero: each generator contributes `λ s` at
the identity and `-λ s` at `s`. -/
theorem sum_coe_laplacian (lam : RateFn G) : ∑ g : G, co (laplacian lam) g = 0 := by
  classical
  have hterm : ∀ g : G, co (laplacian lam) g
      = (if g = 1 then ∑ s : G, lam s else 0) - lam g := coe_laplacian lam
  rw [Finset.sum_congr rfl fun g _ ↦ hterm g, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (1 : G) (fun _ => ∑ s : G, lam s)]
  simp

set_option linter.unusedDecidableInType false in
/-- The Laplacian annihilates the uniform element, on both sides. -/
theorem laplacian_mul_uniform (lam : RateFn G) :
    laplacian lam * uniform G = 0 := by
  rw [uniform_absorb, sum_coe_laplacian, zero_smul]

set_option linter.unusedDecidableInType false in
theorem uniform_mul_laplacian (lam : RateFn G) :
    uniform G * laplacian lam = 0 := by
  rw [uniform_mul_absorb, sum_coe_laplacian, zero_smul]

/-! ### The total rate and the jump element -/

set_option linter.unusedSectionVars false in
/-- The **total rate** `Λ_λ = ∑ s, λ s`. -/
@[lyons_tag "def_total_rate"]
noncomputable def totalRate (lam : RateFn G) : ℝ := ∑ s : G, lam s

/-- The **jump element** `w_λ = ∑ s, λ s · s`. -/
@[lyons_tag "def_total_rate"]
noncomputable def jumpElt (lam : RateFn G) : MonoidAlgebra ℝ G :=
  ∑ s : G, MonoidAlgebra.single s (lam s)

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
@[simp] theorem co_jumpElt (lam : RateFn G) (g : G) : co (jumpElt lam) g = lam g := by
  classical
  rw [jumpElt, co_sum, Finset.sum_eq_single g]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hcon; exact absurd (Finset.mem_univ g) hcon

set_option linter.unusedDecidableInType false in
/-- **The Laplacian splits as total rate minus jump element.** -/
@[lyons_tag "lem_laplacian_split"]
theorem laplacian_eq_totalRate_sub_jumpElt (lam : RateFn G) :
    laplacian lam = totalRate lam • (1 : MonoidAlgebra ℝ G) - jumpElt lam := by
  refine co_injective fun g ↦ ?_
  rw [coe_laplacian, co_sub, co_smul, co_one, co_jumpElt, totalRate]
  by_cases hg : g = 1 <;> simp [hg]

/-! ### The heat element -/

/-- The heat matrix commutes with every right translation, because its generator
does and the exponential preserves commutation. -/
theorem heatMat_commutes_R (lam : RateFn G) (t : ℝ) (h : G) :
    Commute (heatMat lam t) (R h) := by
  have hL : Commute (L (laplacian lam)) (R h) := L_commutes_R _ h
  exact (hL.smul_left (-(t : ℂ))).exp_left

/-- Hence its entries depend only on `g * g'⁻¹`. -/
theorem heatMat_conv (lam : RateFn G) (t : ℝ) (g g' : G) :
    heatMat lam t g g' = heatMat lam t (g * g'⁻¹) 1 :=
  (commutes_R_iff _).mp (heatMat_commutes_R lam t) g g'

/-- **The heat element** `h_t^λ`, the group-algebra element whose coefficient
function is the transition function. -/
noncomputable def heatElt (lam : RateFn G) (t : ℝ) : MonoidAlgebra ℝ G :=
  ofFun (heatCoeffReal lam t)

@[simp] theorem co_heatElt (lam : RateFn G) (t : ℝ) (g : G) :
    co (heatElt lam t) g = heatCoeffReal lam t g := co_ofFun _ g

/-- **The heat element represents the heat matrix.** The two inputs are that the
entries depend only on `g * g'⁻¹` and that they are real. -/
theorem L_heatElt (lam : RateFn G) (t : ℝ) : L (heatElt lam t) = heatMat lam t := by
  ext g h
  have hreal : (heatMat lam t (g * h⁻¹) 1).im = 0 := heatCoeff_im lam t _
  rw [L_apply, co_heatElt, heatCoeffReal, heatMat_conv lam t g h]
  apply Complex.ext <;> simp [heatCoeff, hreal]

/-! ### Absorption -/

/-- **The heat element absorbs the uniform element**, on the right. -/
theorem heatElt_mul_uniform (lam : RateFn G) (t : ℝ) :
    heatElt lam t * uniform G = uniform G := by
  refine L_injective ?_
  rw [L_mul, L_heatElt, heatMat]
  refine exp_mul_of_mul_eq_zero ?_
  rw [smul_mul_assoc, ← L_mul, laplacian_mul_uniform, L_zero, smul_zero]

/-- **The heat element absorbs the uniform element**, on the left. -/
theorem uniform_mul_heatElt (lam : RateFn G) (t : ℝ) :
    uniform G * heatElt lam t = uniform G := by
  refine L_injective ?_
  rw [L_mul, L_heatElt, heatMat]
  refine mul_exp_of_mul_eq_zero ?_
  rw [mul_smul_comm, ← L_mul, uniform_mul_laplacian, L_zero, smul_zero]

/-- **The heat element absorbs the uniform element**, on both sides. -/
@[lyons_tag "lem_heat_absorb"]
theorem heatElt_absorb (lam : RateFn G) (t : ℝ) :
    heatElt lam t * uniform G = uniform G ∧ uniform G * heatElt lam t = uniform G :=
  ⟨heatElt_mul_uniform lam t, uniform_mul_heatElt lam t⟩

/-- **The transition function sums to one.**

Derived from absorption rather than the other way round: `Lyons.coe_mul_uniform`
turns the coefficient sum into `|G|` times one coefficient of
`h_t^λ π_G`, which absorption identifies with `π_G`. -/
@[lyons_tag "lem_heat_coeff_sum_one"]
theorem sum_heatCoeffReal (lam : RateFn G) (t : ℝ) :
    ∑ g : G, heatCoeffReal lam t g = 1 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := congrArg (fun x => co x (1 : G)) (heatElt_mul_uniform lam t)
  simp only [coe_mul_uniform, coe_uniform, co_heatElt] at h
  field_simp at h
  exact h

end Lyons
