/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Lyons.Meta.Tag

/-!
# Eigenvalue powers of a dihedral block, and the scalar inequality

Elementary real arithmetic feeding the reflection inequality. A self-adjoint
`2 × 2` dihedral block has eigenvalues `U ± w`; raising them to `θ` and to
`1 - θ` produces the four numbers `α, β, γ, δ` that the block computation needs.

## Main definitions

* `Lyons.bpAlpha`, `bpBeta`, `bpGamma`, `bpDelta` : the four eigenvalue powers.

## Main results

* `Lyons.bp_nonneg` : all four are nonnegative when `U ≥ w ≥ 0`.
* `Lyons.scalar_ineq` : `A^k B + A B^k ≤ A^{k+1} + B^{k+1}` for `A, B ≥ 0`.
-/

namespace Lyons

/-! ### The four eigenvalue powers -/

/-- Half-sum of the `θ`-th powers of the two eigenvalues. -/
@[lyons_tag "def_block_powers"]
noncomputable def bpAlpha (U w θ : ℝ) : ℝ := ((U + w) ^ θ + (U - w) ^ θ) / 2

/-- Half-difference of the `θ`-th powers. -/
@[lyons_tag "def_block_powers"]
noncomputable def bpBeta (U w θ : ℝ) : ℝ := ((U + w) ^ θ - (U - w) ^ θ) / 2

/-- Half-sum of the `(1-θ)`-th powers. -/
@[lyons_tag "def_block_powers"]
noncomputable def bpGamma (U w θ : ℝ) : ℝ :=
  ((U + w) ^ (1 - θ) + (U - w) ^ (1 - θ)) / 2

/-- Half-difference of the `(1-θ)`-th powers. -/
@[lyons_tag "def_block_powers"]
noncomputable def bpDelta (U w θ : ℝ) : ℝ :=
  ((U + w) ^ (1 - θ) - (U - w) ^ (1 - θ)) / 2

/-- `γ` is `α` at the complementary exponent. Only `α` and `β` occur in
`Lyons.blockM_cfc_rpow`, so every use of that lemma at exponent `1 - θ` needs
this bridge. -/
theorem bpAlpha_one_sub (U w θ : ℝ) : bpAlpha U w (1 - θ) = bpGamma U w θ := rfl

/-- `δ` is `β` at the complementary exponent. -/
theorem bpBeta_one_sub (U w θ : ℝ) : bpBeta U w (1 - θ) = bpDelta U w θ := rfl

section
variable {U w θ : ℝ}

/-- The two eigenvalues are nonnegative and ordered. -/
theorem bp_eigen_nonneg (hw : 0 ≤ w) (hUw : w ≤ U) :
    0 ≤ U - w ∧ U - w ≤ U + w := ⟨by linarith, by linarith⟩

/-- All four eigenvalue powers are nonnegative. -/
@[lyons_tag "lem_block_powers_nonneg"]
theorem bp_nonneg (hw : 0 ≤ w) (hUw : w ≤ U) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    0 ≤ bpAlpha U w θ ∧ 0 ≤ bpBeta U w θ ∧
      0 ≤ bpGamma U w θ ∧ 0 ≤ bpDelta U w θ := by
  obtain ⟨hlo, hord⟩ := bp_eigen_nonneg hw hUw
  have hmono : ∀ e : ℝ, 0 ≤ e → (U - w) ^ e ≤ (U + w) ^ e := fun e he =>
    Real.rpow_le_rpow hlo hord he
  have h1 : (0 : ℝ) ≤ (U - w) ^ θ := Real.rpow_nonneg hlo θ
  have h2 : (0 : ℝ) ≤ (U - w) ^ (1 - θ) := Real.rpow_nonneg hlo (1 - θ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hmono θ hθ; unfold bpAlpha; linarith
  · have := hmono θ hθ; unfold bpBeta; linarith
  · have := hmono (1 - θ) (by linarith); unfold bpGamma; linarith
  · have := hmono (1 - θ) (by linarith); unfold bpDelta; linarith

end

/-- **The scalar inequality** behind the reflection bound.

Stated for an arbitrary natural exponent `k`, not just for odd `k = 2m - 1`: the
proof only needs `t ↦ t ^ k` to be monotone on `[0, ∞)`, and stating it this way
keeps the truncated subtraction `2 * m - 1` out of the statement. -/
@[lyons_tag "lem_scalar_ineq"]
theorem scalar_ineq {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    A ^ k * B + A * B ^ k ≤ A ^ (k + 1) + B ^ (k + 1) := by
  rcases le_total B A with h | h
  · have hp : B ^ k ≤ A ^ k := pow_le_pow_left₀ hB h k
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hp), pow_succ A k, pow_succ B k]
  · have hp : A ^ k ≤ B ^ k := pow_le_pow_left₀ hA h k
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hp), pow_succ A k, pow_succ B k]

/-! ### The two relations between the eigenvalue powers

These are what the sandwich computation actually consumes: the diagonal of
`M^θ ρ(b) M^{1-θ}` is governed by `αγ + βδ` and the off-diagonal by `αδ + βγ`.
Both collapse because `μ^θ · μ^{1-θ} = μ`. -/

section Relations
variable {U w θ : ℝ}

/-- `μ₊ ^ θ * μ₊ ^ (1 - θ) = μ₊`, and likewise for `μ₋`. The nonstandard form of
`Real.rpow_add'` — nonnegative base, nonzero exponent sum — is what makes this
work when `U = w`, where the base is `0` and `Real.rpow_add` would not apply. -/
theorem rpow_theta_mul (hμ : 0 ≤ U) : U ^ θ * U ^ (1 - θ) = U := by
  rw [← Real.rpow_add' hμ (by norm_num), add_sub_cancel]
  exact Real.rpow_one U

/-- **Diagonal relation:** `αγ + βδ = U`. -/
@[lyons_tag "lem_block_rel_diag"]
theorem bp_rel_diag (hw : 0 ≤ w) (hUw : w ≤ U) :
    bpAlpha U w θ * bpGamma U w θ + bpBeta U w θ * bpDelta U w θ = U := by
  have hp : (0 : ℝ) ≤ U + w := by linarith
  have hm : (0 : ℝ) ≤ U - w := by linarith
  have e1 : (U + w) ^ θ * (U + w) ^ (1 - θ) = U + w := rpow_theta_mul hp
  have e2 : (U - w) ^ θ * (U - w) ^ (1 - θ) = U - w := rpow_theta_mul hm
  unfold bpAlpha bpGamma bpBeta bpDelta
  nlinarith [e1, e2]

/-- **Off-diagonal relation:** `αδ + βγ = w`. -/
@[lyons_tag "lem_block_rel_off"]
theorem bp_rel_off (hw : 0 ≤ w) (hUw : w ≤ U) :
    bpAlpha U w θ * bpDelta U w θ + bpBeta U w θ * bpGamma U w θ = w := by
  have hp : (0 : ℝ) ≤ U + w := by linarith
  have hm : (0 : ℝ) ≤ U - w := by linarith
  have e1 : (U + w) ^ θ * (U + w) ^ (1 - θ) = U + w := rpow_theta_mul hp
  have e2 : (U - w) ^ θ * (U - w) ^ (1 - θ) = U - w := rpow_theta_mul hm
  unfold bpAlpha bpDelta bpBeta bpGamma
  nlinarith [e1, e2]

end Relations

end Lyons
