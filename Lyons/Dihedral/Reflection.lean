/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Analysis.Holder
import Lyons.Dihedral.SandwichBlock

/-!
# The reflection inequality

For positive self-adjoint `a` and `θ ∈ [0,1]`,

`∑_g a_g^{2m-1} (x_{a,θ})_g ≤ ∑_g a_g^{2m}`.

## The shape of the argument

Split both sums along the dihedral normal form. On the rotation half the sandwich
is invisible (`Lyons.sum_rotCoeff_pow_mul_sandwich`), so that term becomes a
rotation-against-reflection pairing. Hölder bounds each of the two halves by a
product of counting norms, `Lyons.sum_norm_reflCoeff_sandwich_le` replaces the
sandwich's norm by `‖u^a‖`, and `Lyons.scalar_ineq` collapses
`A^{2m-1}B + AB^{2m-1}` to `A^{2m} + B^{2m}` — which is the right-hand side
reassembled.

## Exponents

Stated with `2 * p + 1` and `2 * p + 2` rather than with `2m - 1` and `2m` (so
`m = p + 1`). Truncated natural subtraction in an exponent is a liability in
every rewrite that touches it, and the two forms are interchangeable under
`m ≥ 1`.

## Main results

* `Lyons.sum_coeff_split` : the normal-form split.
* `Lyons.sum_co_pow_mul_sandwich_le` : the reflection inequality.
-/

open DihedralGroup Finset

namespace Lyons

variable {n : ℕ} [NeZero n]

/-- **Splitting a coefficient sum along the dihedral normal form.**

No hypothesis `Ψ 0 = 0` is needed: that would be required only if the sums were
taken over supports, whereas here they are taken over all of the (finite) index
types, where the reindexing is unconditional. -/
@[lyons_tag "lem_coeff_split"]
theorem sum_coeff_split {M : Type*} [AddCommMonoid M]
    (a : MonoidAlgebra ℝ (DihedralGroup n)) (Ψ : ℝ → M) :
    ∑ g : DihedralGroup n, Ψ (co a g)
      = (∑ j : ZMod n, Ψ (co a (.r j))) + ∑ j : ZMod n, Ψ (co a (.sr j)) :=
  sum_dihedral _

section

variable (a : MonoidAlgebra ℝ (DihedralGroup n)) (hpos : IsPos a)
  {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)

include hpos hθ hθ'

/-- The rotation-half pairing, with real coefficients. `Lyons.rotCoeff` and
`Lyons.reflCoeff` are `ℂ`-valued because they arise as matrix entries; the
identity they satisfy is the coercion of this real one, and coercion is
injective. -/
theorem sum_co_pow_mul_sandwich (p : ℕ) :
    ∑ j : ZMod n, co a (.r j) ^ p * co (sandwich a (sr 0) θ) (.r j)
      = ∑ j : ZMod n, co a (.r j) ^ p * co a (.sr j) := by
  have h := sum_rotCoeff_pow_mul_sandwich a hpos hθ hθ' p
  simp only [rotCoeff, reflCoeff] at h
  exact_mod_cast h

/-- The sandwich's reflection coefficients are dominated in counting norm by the
rotation coefficients of `a`. This is `Lyons.sum_norm_reflCoeff_sandwich_le`
pulled back from `‖·‖` on `ℂ` to `|·|` on `ℝ`, and then to the roots. -/
theorem rootSum_co_sandwich_le (p : ℕ) :
    rootSum univ (fun j : ZMod n => |co (sandwich a (sr 0) θ) (.sr j)|) (2 * p)
      ≤ rootSum univ (fun j : ZMod n => |co a (.r j)|) (2 * p) := by
  refine rootSum_le_rootSum (fun j _ => abs_nonneg _) ?_
  have h := sum_norm_reflCoeff_sandwich_le a hpos hθ hθ' (m := p + 1)
    (Nat.le_add_left 1 p)
  simpa [reflCoeff, rotCoeff, Nat.mul_succ] using h

/-- **The reflection inequality.** The version over the inversion extension of a
general finite abelian group, at an arbitrary outside element, is
`Lyons.InvExtBlock.sum_co_pow_mul_sandwich_le`. -/
theorem sum_co_pow_mul_sandwich_le (p : ℕ) :
    ∑ g : DihedralGroup n, co a g ^ (2 * p + 1) * co (sandwich a (sr 0) θ) g
      ≤ ∑ g : DihedralGroup n, co a g ^ (2 * p + 2) := by
  classical
  have hev : Even (2 * p + 2) := ⟨p + 1, by ring⟩
  set A : ℝ := rootSum univ (fun j : ZMod n => |co a (.r j)|) (2 * p) with hA
  set B : ℝ := rootSum univ (fun j : ZMod n => |co a (.sr j)|) (2 * p) with hB
  have hA0 : 0 ≤ A := rootSum_nonneg (fun j _ => abs_nonneg _) _
  have hB0 : 0 ≤ B := rootSum_nonneg (fun j _ => abs_nonneg _) _
  -- Each half: pass to absolute values, then Hölder.
  have habs : ∀ f h : ZMod n → ℝ,
      ∑ j : ZMod n, f j ^ (2 * p + 1) * h j
        ≤ ∑ j : ZMod n, |f j| ^ (2 * p + 1) * |h j| := fun f h =>
    Finset.sum_le_sum fun j _ =>
      (le_abs_self _).trans (by rw [abs_mul, abs_pow])
  have hrot : ∑ j : ZMod n, co a (.r j) ^ (2 * p + 1) * co a (.sr j)
      ≤ A ^ (2 * p + 1) * B :=
    (habs _ _).trans (sum_pow_succ_mul_le (fun j _ => abs_nonneg _)
      (fun j _ => abs_nonneg _) (2 * p))
  have hrefl : ∑ j : ZMod n,
        co a (.sr j) ^ (2 * p + 1) * co (sandwich a (sr 0) θ) (.sr j)
      ≤ B ^ (2 * p + 1) * A := by
    refine (habs _ _).trans ?_
    refine (sum_pow_succ_mul_le (fun j _ => abs_nonneg _)
      (fun j _ => abs_nonneg _) (2 * p)).trans ?_
    exact mul_le_mul_of_nonneg_left (rootSum_co_sandwich_le a hpos hθ hθ' p)
      (pow_nonneg hB0 _)
  calc ∑ g : DihedralGroup n, co a g ^ (2 * p + 1) * co (sandwich a (sr 0) θ) g
      = (∑ j : ZMod n, co a (.r j) ^ (2 * p + 1) *
            co (sandwich a (sr 0) θ) (.r j))
          + ∑ j : ZMod n, co a (.sr j) ^ (2 * p + 1) *
            co (sandwich a (sr 0) θ) (.sr j) := sum_dihedral _
    _ = (∑ j : ZMod n, co a (.r j) ^ (2 * p + 1) * co a (.sr j))
          + ∑ j : ZMod n, co a (.sr j) ^ (2 * p + 1) *
            co (sandwich a (sr 0) θ) (.sr j) := by
        rw [sum_co_pow_mul_sandwich a hpos hθ hθ' (2 * p + 1)]
    _ ≤ A ^ (2 * p + 1) * B + B ^ (2 * p + 1) * A := add_le_add hrot hrefl
    _ ≤ A ^ (2 * p + 2) + B ^ (2 * p + 2) := by
        have := scalar_ineq hA0 hB0 (2 * p + 1)
        nlinarith [this]
    _ = ∑ g : DihedralGroup n, co a g ^ (2 * p + 2) := by
        rw [hA, hB, rootSum_pow (fun j _ => abs_nonneg _),
          rootSum_pow (fun j _ => abs_nonneg _),
          sum_coeff_split a fun t : ℝ => t ^ (2 * p + 2)]
        congr 1 <;> exact Finset.sum_congr rfl fun j _ => hev.pow_abs _

end

end Lyons
