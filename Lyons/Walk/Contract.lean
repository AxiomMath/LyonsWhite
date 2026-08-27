/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Convex.Mul
import Lyons.Walk.Nonneg

/-!
# Convolution by a probability element contracts every even power sum

This is the whole of the rotation half of the main theorem: raising a rotation
rate replaces the centred heat element by its convolution with a probability
element, and that cannot increase `∑ x_g ^ (2m)`.

## Why no sign hypothesis on `x`

None is available. The intended `x` is a centred heat element, whose coefficients
are negative wherever the walk sits below uniform. Jensen at an even exponent
needs no sign: `Even.convexOn_pow` gives convexity of `· ^ (2m)` on all of `ℝ`,
not just on `[0, ∞)`.

## Main results

* `Lyons.co_mul'` : the convolution rule in the `∑ u, x_u y_{u⁻¹ g}` form.
* `Lyons.sum_pow_conv_le` : the contraction.
-/

open Finset

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- The convolution rule with the sum taken over the *left* factor's index.

`Lyons.co_mul` sums over the right factor; this is the same identity reindexed by
`h ↦ g h⁻¹`, and it is the form Jensen is applied to, because the weights must be
the coefficients of the probability element. -/
theorem co_mul' (x y : MonoidAlgebra ℝ G) (g : G) :
    co (x * y) g = ∑ u : G, co x u * co y (u⁻¹ * g) := by
  rw [co_mul]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft g)) _ _ fun h => ?_
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft]
  congr 2
  group

omit [DecidableEq G] in
/-- **Convolution by a probability element contracts the even power sum.**

`κ` is required only to have nonnegative coefficients summing to one — it need not
be a heat element, and `x` is arbitrary. -/
@[lyons_tag "lem_convolution_contracts"]
theorem sum_pow_conv_le (kap x : MonoidAlgebra ℝ G)
    (hk : ∀ g, 0 ≤ co kap g) (hk1 : ∑ g : G, co kap g = 1) (m : ℕ) :
    ∑ g : G, (co (kap * x) g) ^ (2 * m) ≤ ∑ g : G, (co x g) ^ (2 * m) := by
  have hconvex : ConvexOn ℝ Set.univ (fun r : ℝ => r ^ (2 * m)) :=
    Even.convexOn_pow (even_two_mul m)
  -- Jensen at each `g`, with the coefficients of `κ` as the weights.
  have hstep : ∀ g : G, (co (kap * x) g) ^ (2 * m)
      ≤ ∑ u : G, co kap u * (co x (u⁻¹ * g)) ^ (2 * m) := by
    intro g
    rw [co_mul']
    have := hconvex.map_sum_le (t := Finset.univ) (w := fun u => co kap u)
      (p := fun u => co x (u⁻¹ * g)) (fun i _ => hk i) hk1 (fun i _ => Set.mem_univ _)
    simpa using this
  calc ∑ g : G, (co (kap * x) g) ^ (2 * m)
      ≤ ∑ g : G, ∑ u : G, co kap u * (co x (u⁻¹ * g)) ^ (2 * m) :=
        Finset.sum_le_sum fun g _ => hstep g
    _ = ∑ u : G, co kap u * ∑ g : G, (co x (u⁻¹ * g)) ^ (2 * m) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ u : G, co kap u * ∑ g : G, (co x g) ^ (2 * m) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        congr 1
        exact Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ _ fun g => rfl
    _ = ∑ g : G, (co x g) ^ (2 * m) := by rw [← Finset.sum_mul, hk1, one_mul]

end Lyons
