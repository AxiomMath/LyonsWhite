/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.Main
import Lyons.Walk.Relabel

/-!
# Even-exponent monotonicity on dihedral groups, in power-sum form

`Lyons.sum_abs_centered_pow_le` is the dihedral power-sum inequality: the sums
`∑_g |p_t^λ(g) - 1/(2n)|^{2m}` are nonincreasing in the rates.

Every step of the argument happens over the inversion extension `G_{ℤ/n, 0}`,
and the conclusion is carried across `Lyons.InvExt.dihedralEquiv` by
`Lyons.Phi_comp`.

## Main results

* `Lyons.Phi_eq_sum_abs` : `Lyons.Phi` as a sum of absolute values.
* `Lyons.sum_abs_centered_pow_le` : monotonicity of the centred power sums.
-/

open Finset DihedralGroup

namespace Lyons

variable {n : ℕ} [NeZero n]

set_option linter.unusedDecidableInType false in
/-- `Lyons.Phi` as a sum of absolute values: `|p_t^λ(g) - 1/(2n)|^{2m}`, summed
over the group. -/
theorem Phi_eq_sum_abs (lam : RateFn (DihedralGroup n)) (t : ℝ) (m : ℕ) :
    Phi lam t m
      = ∑ g : DihedralGroup n, |heatCoeffReal lam t g - (2 * n : ℝ)⁻¹| ^ (2 * m) := by
  rw [Phi_eq_sum_real]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hcard : (Fintype.card (DihedralGroup n) : ℝ) = 2 * n := by
    rw [DihedralGroup.card]; push_cast; ring
  rw [centeredHeatCoeffReal, hcard, pow_mul, ← sq_abs, ← pow_mul]

set_option linter.unusedDecidableInType false in
/-- **Even-exponent monotonicity on dihedral groups**, in power-sum form.

Proved by relabelling both rate functions along `Lyons.InvExt.dihedralEquiv` and
applying `Lyons.Phi_le_of_le` over the inversion extension, where the whole
argument lives.

`p_t^λ` is `Lyons.heatCoeffReal`, the first column of `exp (-t Δ_λ)`;
`Lyons.heatCoeffReal_nonneg`, `Lyons.sum_heatCoeffReal` and
`Lyons.hasDerivAt_heatCoeffReal_forward` are what license reading it as a
transition probability. -/
theorem sum_abs_centered_pow_le (lam mu : RateFn (DihedralGroup n))
    (hle : ∀ g : DihedralGroup n, g ≠ 1 → lam g ≤ mu g) {t : ℝ} (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) :
    ∑ g : DihedralGroup n, |heatCoeffReal mu t g - (2 * n : ℝ)⁻¹| ^ (2 * m)
      ≤ ∑ g : DihedralGroup n, |heatCoeffReal lam t g - (2 * n : ℝ)⁻¹| ^ (2 * m) := by
  set φ : InvExt (ZMod n) 0 ≃* DihedralGroup n := InvExt.dihedralEquiv with hφ
  have hle' : ∀ x : InvExt (ZMod n) 0, x ≠ 1 → lam.comp φ x ≤ mu.comp φ x := by
    intro x hx
    have hiff : φ x = 1 ↔ x = 1 := map_eq_one_iff φ.toMonoidHom φ.injective
    rw [RateFn.comp_apply, RateFn.comp_apply]
    exact hle (φ x) (fun hcon => hx (hiff.mp hcon))
  have hkey := Phi_le_of_le (lam.comp φ) (mu.comp φ) hle' ht hm
  rw [Phi_comp lam φ, Phi_comp mu φ, Phi_eq_sum_abs, Phi_eq_sum_abs] at hkey
  exact hkey

end Lyons
