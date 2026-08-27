/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.MeanInequalities
import Lyons.Meta.Tag

/-!
# Hölder's inequality in counting-norm form

Mathlib's `Real.inner_le_Lp_mul_Lq_of_nonneg` is Hölder's inequality with the two
exponents given as arbitrary reals in `HolderConjugate` position, and with the
powers taken as `Real.rpow`. Section 4 of the paper uses it in one specific
shape: exponents `2m/(2m-1)` and `2m`, natural powers, and the `2m`-th root of a
sum in place of a norm.

Bridging the two is pure exponent arithmetic, and it is a surprising amount of
it, so it is isolated here rather than inlined at the one place it is used.

## The parametrisation

Everything is indexed by `k : ℕ` with the "large" exponent being `k + 2`, so the
conjugate `k + 1` is a numeral-free natural number and no truncated subtraction
`2 * m - 1` appears anywhere. The substitution against the usual form with
exponents `2m` and `2m - 1` is `k + 2 = 2m`.

## Main results

* `Lyons.rootSum` : the `(k+2)`-th root of `∑ f i ^ (k+2)`, i.e. the counting
  `ℓ^{k+2}` norm of a nonnegative family.
* `Lyons.rootSum_pow` : it recovers the sum on raising to the `(k+2)`-th power.
* `Lyons.sum_pow_succ_mul_le` : Hölder.
-/

open Finset

namespace Lyons

variable {ι : Type*} (s : Finset ι)

/-- The counting `ℓ^{k+2}` norm of a family of reals: the `(k+2)`-th root of
`∑ f i ^ (k+2)`. Written with `Real.rpow` because the root is not a natural
power. -/
noncomputable def rootSum (f : ι → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ s, f i ^ (k + 2)) ^ (((k + 2 : ℕ) : ℝ)⁻¹)

variable {s}

/-- The sum of even powers of reals is nonnegative — and for `f` nonnegative,
so is any sum of powers. -/
theorem sum_pow_nonneg {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (m : ℕ) :
    (0 : ℝ) ≤ ∑ i ∈ s, f i ^ m :=
  Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) m

theorem rootSum_nonneg {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (k : ℕ) :
    0 ≤ rootSum s f k :=
  Real.rpow_nonneg (sum_pow_nonneg hf _) _

/-- Raising the root back to the `(k+2)`-th power recovers the sum. -/
theorem rootSum_pow {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (k : ℕ) :
    rootSum s f k ^ (k + 2) = ∑ i ∈ s, f i ^ (k + 2) := by
  have hq : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [rootSum, ← Real.rpow_natCast (_ ^ _) (k + 2),
    ← Real.rpow_mul (sum_pow_nonneg hf _)]
  rw [show (((k + 2 : ℕ) : ℝ)⁻¹ * ((k + 2 : ℕ) : ℝ)) = 1 from inv_mul_cancel₀ hq,
    Real.rpow_one]

/-- Monotonicity of the root in the sum. -/
theorem rootSum_le_rootSum {f g : ι → ℝ} {k : ℕ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (h : ∑ i ∈ s, f i ^ (k + 2) ≤ ∑ i ∈ s, g i ^ (k + 2)) :
    rootSum s f k ≤ rootSum s g k :=
  Real.rpow_le_rpow (sum_pow_nonneg hf _) h (by positivity)

/-- **Hölder's inequality**, in the counting-norm shape §4 uses.

Mathlib supplies the analytic content, `Real.inner_le_Lp_mul_Lq_of_nonneg`; what
it does not supply is this statement, whose exponents are natural powers and
whose right-hand side is a product of roots-of-sums rather than of `rpow`s of
sums. -/
@[lyons_tag "lem_ext_holder"]
theorem sum_pow_succ_mul_le {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) (k : ℕ) :
    ∑ i ∈ s, f i ^ (k + 1) * g i
      ≤ rootSum s f k ^ (k + 1) * rootSum s g k := by
  have hqne : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq1 : (1 : ℝ) < ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
  -- Take the conjugate exponent without naming it: only these two identities of
  -- it are ever used, and both come straight from `HolderConjugate`.
  obtain ⟨p, hcq⟩ : ∃ p : ℝ, (((k + 2 : ℕ) : ℝ)).HolderConjugate p :=
    ⟨_, Real.HolderConjugate.conjExponent hq1⟩
  have hsub : (((k + 2 : ℕ) : ℝ) - 1) * p = ((k + 2 : ℕ) : ℝ) := hcq.sub_one_mul_conj
  have hinv : p⁻¹ + ((k + 2 : ℕ) : ℝ)⁻¹ = 1 := hcq.symm.inv_add_inv_eq_one
  -- The `f`-side exponent `k + 1` is `(k + 2) - 1`.
  have hk1 : ((k + 1 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) - 1 := by push_cast; ring
  -- Mathlib's Hölder, with the `(k+1)`-st power of `f` as the first family.
  have hF : ∀ i ∈ s, (0 : ℝ) ≤ f i ^ (k + 1) := fun i hi => pow_nonneg (hf i hi) _
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (p := p) (q := ((k + 2 : ℕ) : ℝ)) hcq.symm hF hg
  -- Rewrite the two `rpow`ed summands into natural powers.
  have hfp : ∀ i ∈ s, (f i ^ (k + 1)) ^ p = f i ^ (k + 2) := fun i hi => by
    rw [← Real.rpow_natCast (f i) (k + 1), ← Real.rpow_mul (hf i hi), hk1, hsub,
      Real.rpow_natCast]
  have hgq : ∀ i ∈ s, g i ^ ((k + 2 : ℕ) : ℝ) = g i ^ (k + 2) := fun i _ =>
    Real.rpow_natCast (g i) (k + 2)
  rw [Finset.sum_congr rfl hfp, Finset.sum_congr rfl hgq] at key
  refine key.trans (le_of_eq ?_)
  -- `1/(k+2)` is the root's exponent, and `1/p` is `(k+1)` times it.
  have hexp : 1 / p = ((k + 2 : ℕ) : ℝ)⁻¹ * ((k + 1 : ℕ) : ℝ) := by
    have hp' : p⁻¹ = 1 - ((k + 2 : ℕ) : ℝ)⁻¹ := by linarith
    rw [one_div, hp']
    field_simp
    push_cast
    ring
  rw [rootSum, rootSum, ← Real.rpow_natCast (_ ^ ((k + 2 : ℕ) : ℝ)⁻¹) (k + 1),
    ← Real.rpow_mul (sum_pow_nonneg hf _), ← hexp]
  simp only [one_div]

end Lyons
