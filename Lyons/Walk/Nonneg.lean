/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Lyons.Walk.Increment

/-!
# The transition function is nonnegative

Together with `Lyons.sum_heatCoeffReal` and the Kolmogorov forward equation this
is what licenses calling `p_t^λ` a *transition function* at all: it is **defined**
here as an entry of a matrix exponential, whereas the paper defines it as a
probability. Without these three the main theorem is a statement about a matrix
entry, not about a distribution.

## The argument

`Δ_λ = Λ_λ · 1 - w_λ` splits the generator into a scalar and the jump element,
whose coefficients are the rates and so are nonnegative. The scalar commutes with
everything, so

`exp (-t Δ_λ) = e^{-tΛ_λ} · exp (t w_λ)`,

and every entry of `exp (t w_λ)` is a limit of partial sums of matrices with
nonnegative entries. `ComplexOrder` makes "nonnegative entry" a genuine order
fact (`0 ≤ z` there means `0 ≤ z.re ∧ z.im = 0`, so it carries realness too), and
that order is closed, which is what lets the limit inherit it.

`0 ≤ t` is load-bearing: for negative time the walk runs backwards and the
coefficients go negative.

## Main results

* `Lyons.exp_entry_nonneg` : the exponential of an entrywise-nonnegative matrix is
  entrywise nonnegative.
* `Lyons.heatCoeffReal_nonneg` : `0 ≤ p_t^λ(g)`.
-/

open Matrix
open scoped ComplexOrder Norms.Operator

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Entrywise nonnegativity survives products and the exponential -/

omit [Group G] in
/-- Powers of an entrywise-nonnegative matrix are entrywise nonnegative. -/
theorem pow_entry_nonneg {B : Matrix G G ℂ} (hB : ∀ g h, 0 ≤ B g h) :
    ∀ (n : ℕ) (g h : G), 0 ≤ (B ^ n) g h := by
  intro n
  induction n with
  | zero =>
    intro g h
    rw [pow_zero]
    by_cases hgh : g = h <;> simp [Matrix.one_apply, hgh]
  | succ k ih =>
    intro g h
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun u _ => mul_nonneg (ih g u) (hB u h)

omit [Group G] in
/-- **The exponential of an entrywise-nonnegative matrix is entrywise
nonnegative.**

Each partial sum of the exponential series has nonnegative entries, entry
evaluation is continuous, and the order on `ℂ` supplied by `ComplexOrder` is
closed — so the limit keeps the bound. -/
theorem exp_entry_nonneg {B : Matrix G G ℂ} (hB : ∀ g h, 0 ≤ B g h) (g h : G) :
    0 ≤ NormedSpace.exp B g h := by
  have hs : Summable (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) • B ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) B
  have hsum : HasSum (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) • B ^ n)
      (NormedSpace.exp B) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    exact hs.hasSum
  have hc : Continuous (fun M : Matrix G G ℂ => M g h) := by fun_prop
  refine ge_of_tendsto ((hc.tendsto _).comp hsum.tendsto_sum_nat) ?_
  filter_upwards with n
  rw [Function.comp_apply, Matrix.sum_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Matrix.smul_apply, Complex.real_smul]
  exact mul_nonneg (Complex.zero_le_real.mpr (by positivity))
    (pow_entry_nonneg hB i g h)

/-! ### Splitting off the scalar part of the generator -/

omit [Group G] in
/-- The exponential of a scalar matrix is the scalar exponential. -/
theorem exp_smul_one (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix G G ℂ))
      = (NormedSpace.exp z) • (1 : Matrix G G ℂ) := by
  have hd : z • (1 : Matrix G G ℂ) = Matrix.diagonal (fun _ : G => z) := by
    ext g h
    by_cases hgh : g = h <;> simp [hgh]
  rw [hd, Matrix.exp_diagonal]
  ext g h
  by_cases hgh : g = h <;> simp [hgh, Pi.coe_exp]

set_option linter.unusedDecidableInType false in
/-- The generator splits as a scalar plus a nonnegative part. -/
theorem smul_L_laplacian_eq (lam : RateFn G) (t : ℝ) :
    -(t : ℂ) • L (laplacian lam)
      = ((-(t * totalRate lam) : ℝ) : ℂ) • (1 : Matrix G G ℂ)
        + (t : ℂ) • L (jumpElt lam) := by
  rw [laplacian_eq_totalRate_sub_jumpElt, L_sub, L_smul, L_one]
  ext g h
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
  ring

set_option linter.unusedDecidableInType false in
/-- **The heat matrix is a positive scalar times the exponential of the jump
element.** -/
theorem heatMat_eq_smul_exp_jumpElt (lam : RateFn G) (t : ℝ) :
    heatMat lam t
      = (NormedSpace.exp ((-(t * totalRate lam) : ℝ) : ℂ))
          • NormedSpace.exp ((t : ℂ) • L (jumpElt lam)) := by
  have hcomm : Commute (((-(t * totalRate lam) : ℝ) : ℂ) • (1 : Matrix G G ℂ))
      ((t : ℂ) • L (jumpElt lam)) := (Commute.one_left _).smul_left _
  rw [heatMat, smul_L_laplacian_eq, Matrix.exp_add_of_commute _ _ hcomm,
    exp_smul_one, smul_mul_assoc, one_mul]

/-! ### Nonnegativity -/

set_option linter.unusedDecidableInType false in
/-- Every entry of the heat matrix is nonnegative, for nonnegative time. -/
theorem heatMat_entry_nonneg (lam : RateFn G) {t : ℝ} (ht : 0 ≤ t) (g h : G) :
    0 ≤ heatMat lam t g h := by
  have hjump : ∀ u v : G, 0 ≤ ((t : ℂ) • L (jumpElt lam)) u v := by
    intro u v
    rw [Matrix.smul_apply, smul_eq_mul, L_apply, co_jumpElt]
    exact mul_nonneg (Complex.zero_le_real.mpr ht)
      (Complex.zero_le_real.mpr (lam.nonneg _))
  rw [heatMat_eq_smul_exp_jumpElt, Matrix.smul_apply, smul_eq_mul]
  refine mul_nonneg ?_ (exp_entry_nonneg hjump g h)
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
  exact Complex.zero_le_real.mpr (Real.exp_nonneg _)

set_option linter.unusedDecidableInType false in
/-- **The transition function is nonnegative.**

With `Lyons.sum_heatCoeffReal` this says the coefficients of `h_t^λ` are a
probability distribution on `G`. -/
@[lyons_tag "lem_heat_coeff_nonneg"]
theorem heatCoeffReal_nonneg (lam : RateFn G) {t : ℝ} (ht : 0 ≤ t) (g : G) :
    0 ≤ heatCoeffReal lam t g :=
  (Complex.nonneg_iff.mp (heatMat_entry_nonneg lam ht g 1)).1

end Lyons
