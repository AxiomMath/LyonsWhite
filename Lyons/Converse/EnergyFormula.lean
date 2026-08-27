/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Energy
import Lyons.Converse.Sandwich
import Lyons.Converse.TrigSums

/-!
# The energy at the test element

The closed form of `𝓔_p(ξ_{n,K,ε}; τ)`, its first-order behaviour as `ε → 0⁺`,
and the positivity that breaks rate-monotonicity.

Throughout, `κ = 2/n`, and for `j ∈ ℤ/n`

  `y_j = cos(2πj/n)`,  `Y_j = cos(2πKj/n)`,  `S_j = sin(2πKj/n)`.

The mechanism is one line: `Lyons.Converse.sandwich_testElement` says the
sandwich `S_{ξ_{n,K,ε},θ,τ}` is `ξ_{n,K,0}` for **every** `θ ∈ (0,1)`. So the
integrand of `Lyons.Converse.energy` does not depend on `θ` at all, and the
integral over an interval of length `1` is that one constant value. That collapse
is what makes the energy computable in closed form; everything after it is
bookkeeping on coefficients.

## Main results

* `Lyons.Converse.energy_testElement` : the closed form of the energy.
* `Lyons.Converse.tendsto_energy_testElement_div` : the limit of `𝓔_p/ε` as
  `ε → 0⁺`.
* `Lyons.Converse.exists_energy_testElement_pos` : the energy is positive for
  every sufficiently small `ε > 0`.

`Lyons.Converse.energy_of_sandwich_const` is the first step of the closed-form
computation, separated out because it is a statement about the energy of an
arbitrary element whose sandwich happens to be constant on `(0,1)`, with nothing
about the test element in it.

## Implementation notes

The conventions are the standing ones of the files this builds on
(`Lyons.Converse.TestElement`, `Lyons.Converse.Sandwich`), reused
verbatim rather than reinvented.

*The cyclic group is `ZMod n`, written additively.* Rather than an abstract
cyclic `C` of order `n` with a generator `c` and sums over `j ∈ ℤ/n` indexed by
`c^j`, here `C = ZMod n` with `c = 1`, so `c^j` is the residue `j` and the
reindexing bijection is the identity. Likewise `z = 1` becomes `z = 0` and the
outside index `d = 1` becomes `d = 0`, so the group is
`Lyons.InvExt (ZMod n) 0`, the reflection `τ` is
`Lyons.InvExt.b = InvExt.refl 0`, and `u^x(c^j)` and `v^{x,1}(c^j)` are
`co x (.rot j)` and `co x (.refl j)`.

*The angles are read at the `ZMod.val` lift.* For `j ∈ ℤ/n` the value
`cos(2πj/n)` is read by lifting `j` to an integer, and is independent of the
lift; the lift is fixed to `ZMod.val` here, which is the convention of
`Lyons.Converse.TestElement` and `Lyons.Converse.TrigSums`, so that
`Lyons.Converse.co_testElement_rot` and
`Lyons.Converse.sum_signedPow_cos_mul_sin` apply to these sums verbatim.

*`K ≥ 2` suffices.* Inherited, not chosen: `hK` and `hn` enter only through
`Lyons.Converse.sandwich_testElement` and `Lyons.Converse.isPos_testElement`,
neither of which asks for more.

*`n > 2K` is written `2 * K < (n : ℤ)`.* The comparison is in `ℤ` because
`K : ℤ`; this is the shape every lemma about the test element is stated at.

*`(2/n)^p` is `Real.rpow`.* The exponent `p` is real, as it must be: the point of
the whole argument is a *non-even* exponent.

*The closed form is written `-(κ^p * ε * ∑ …)`, one negation of one product,*
rather than `-(2/n)^p ε ∑ …`. The two are the same number; the parenthesised form
removes any question of how a leading minus binds against `rpow`.

*`p ≥ 1` is never assumed.* `Lyons.Converse.signedPow` is defined for every real
`p`, `Lyons.Converse.signedPow_const_mul` and
`Lyons.Converse.continuousAt_signedPow` hold for every real `p`, and no other
property of `J_p` is used, so the hypothesis appears in none of the three
statements below. It is `p ≥ 1` that makes `J_p` the derivative of `|y|^p/p`, and
that is a fact about `J_p`, not about the energy.

*`ε ≥ 0` is assumed in the closed form, and appears in the other two only through
`0 < ε`.* It is genuinely needed: it is what
`Lyons.Converse.isPos_testElement` requires, and the sandwich — hence the
energy — is only `x^θ c x^{1-θ}` at a positive element.

*The limit is taken along `nhdsWithin 0 (Set.Ioi 0)`.* That filter is the
notation `𝓝[>] 0`, i.e. `ε → 0⁺`.
-/
open Finset MeasureTheory Real

namespace Lyons.Converse

/-! ### The energy of an element whose sandwich is constant -/

/-- **If the sandwich does not depend on `θ`, the energy is a single finite sum.**
If `S_{x,θ,c} = y` for every `θ ∈ (0,1)`, then

  `𝓔_p(x; c) = ∑_{g ∈ G} J_p(x_g) (y_g - x_g)`.

This is the first step of the closed-form computation, and the only place the
integral of `Lyons.Converse.energy` is ever evaluated: the integrand is constant,
and the interval has length `1`.

The hypothesis is `θ ∈ (0,1)`, both ends strict, because that is all
`Lyons.Converse.sandwich_testElement` provides. `Set.uIoc 0 1` is `Ioc 0 1`,
which differs from `Ioo 0 1` by the single point `1`, so the two integrands are
compared almost everywhere rather than pointwise — exactly as
`Lyons.Converse.energy_smul` does. The integrand's endpoint values do not affect
the integral. -/
theorem energy_of_sandwich_const {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (p : ℝ) (x y : MonoidAlgebra ℝ G) (c : G)
    (h : ∀ θ : ℝ, 0 < θ → θ < 1 → sandwich x c θ = y) :
    energy p x c = ∑ g : G, signedPow p (co x g) * (co y g - co x g) := by
  rw [energy_def]
  have hI : (∫ θ in (0 : ℝ)..1,
        ∑ g : G, signedPow p (co x g) * (co (sandwich x c θ) g - co x g))
      = ∫ _ in (0 : ℝ)..1, ∑ g : G, signedPow p (co x g) * (co y g - co x g) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (1 : ℝ)]
      with θ hθne hθmem
    rw [Set.uIoc_of_le zero_le_one] at hθmem
    rw [h θ hθmem.1 (lt_of_le_of_ne hθmem.2 hθne)]
  rw [hI, intervalIntegral.integral_const, sub_zero, one_smul]

/-! ### The closed form -/

variable {n : ℕ} [NeZero n]

/-- One summand of the closed form. With `κ > 0`,

  `J_p(κ(y + εt)) · (κ(y + 0·t) - κ(y + εt)) = -(κ^p ε (J_p(y + εt) t))`.

The two homogeneities in one step: the coefficient difference is `-κεt`, and
`Lyons.Converse.signedPow_const_mul` pulls `κ^{p-1}` out of `J_p`, with
`κ^{p-1} · κ = κ^p`.  Both halves of the sum in `energy_testElement` have this
shape — the abelian half at
`t = Y_j` and the outside half at `t = S_j` — which is why it is stated once, in
`t`. The odd-looking `y + 0·t` is literally what
`Lyons.Converse.co_testElement_rot` returns at `ε = 0`. -/
private theorem energy_term {p κ : ℝ} (hκ : 0 < κ) (ε y t : ℝ) :
    signedPow p (κ * (y + ε * t)) * (κ * (y + 0 * t) - κ * (y + ε * t))
      = -(κ ^ p * ε * (signedPow p (y + ε * t) * t)) := by
  have hpow : κ ^ (p - 1) * κ = κ ^ p := by
    rw [Real.rpow_sub hκ, Real.rpow_one, div_mul_cancel₀ _ hκ.ne']
  rw [signedPow_const_mul hκ, ← hpow]
  ring

/-- **Closed form of the energy at the test element.**

  `𝓔_p(ξ_{n,K,ε}; τ) = -((2/n)^p ε ∑_{j ∈ ℤ/n} (J_p(y_j + εY_j) Y_j + J_p(y_j + εS_j) S_j))`

with `y_j = cos(2πj/n)`, `Y_j = cos(2πKj/n)` and `S_j = sin(2πKj/n)`.

`Lyons.Converse.isPos_testElement` makes the energy meaningful;
`Lyons.Converse.sandwich_testElement` makes its integrand constant in `θ`, so
`Lyons.Converse.energy_of_sandwich_const` collapses the integral to
`∑_{g ∈ G} J_p(ξ_g)((ξ_{n,K,0})_g - ξ_g)`; `Lyons.sum_coeff_split_pair` at
`d = 0`, with `Ψ y y' = J_p(y)(y' - y)`, splits that over `G` into two sums over
`ℤ/n`; and `Lyons.Converse.co_testElement_rot` /
`Lyons.Converse.co_testElement_refl` evaluate the coefficients, which
`energy_term` turns into the two displayed summands.

`Ψ` is curried here, since that is how `Lyons.sum_coeff_split_pair` takes it.
See the module docstring for the conventions and for the hypotheses (`K ≥ 2`, no
`p ≥ 1`). -/
@[lyons_tag "lem_Ep_formula"]
theorem energy_testElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) {ε : ℝ}
    (hε : 0 ≤ ε) (p : ℝ) :
    energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0)
      = -((2 / (n : ℝ)) ^ p * ε *
          ∑ j : ZMod n,
            (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)
                  + ε * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))
                * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
              + signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)
                  + ε * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))
                * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hκ : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) hn0
  rw [energy_of_sandwich_const p (testElement n K ε) (testElement n K 0) InvExt.b
    fun _ hθ hθ' => sandwich_testElement hK hn hε hθ hθ']
  calc ∑ g : InvExt (ZMod n) 0, signedPow p (co (testElement n K ε) g)
          * (co (testElement n K 0) g - co (testElement n K ε) g)
      = (∑ a : ZMod n, signedPow p (co (testElement n K ε) (.rot a))
            * (co (testElement n K 0) (.rot a) - co (testElement n K ε) (.rot a)))
        + ∑ a : ZMod n, signedPow p (co (testElement n K ε) (.refl (a + 0)))
            * (co (testElement n K 0) (.refl (a + 0))
              - co (testElement n K ε) (.refl (a + 0))) :=
        sum_coeff_split_pair (testElement n K ε) (testElement n K 0) (0 : ZMod n)
          fun u v => signedPow p u * (v - u)
    _ = (∑ j : ZMod n, -((2 / (n : ℝ)) ^ p * ε *
            (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)
                + ε * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))
              * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))))
          + ∑ j : ZMod n, -((2 / (n : ℝ)) ^ p * ε *
            (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)
                + ε * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))
              * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))) := by
        congr 1
        · refine Finset.sum_congr rfl fun a _ => ?_
          rw [co_testElement_rot, co_testElement_rot, energy_term hκ]
        · refine Finset.sum_congr rfl fun a _ => ?_
          rw [add_zero, co_testElement_refl, co_testElement_refl, energy_term hκ]
    _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### The first order in `ε` -/

/-- **The energy to first order in `ε`.** For odd `n`,

  `lim_{ε → 0⁺} 𝓔_p(ξ_{n,K,ε}; τ)/ε = -((2/n)^p ∑_{j ∈ ℤ/n} J_p(y_j)(Y_j + S_j))`.

Divide `Lyons.Converse.energy_testElement` by `ε ≠ 0`; what is left is a finite
sum of terms `J_p(y_j + εY_j) Y_j` and `J_p(y_j + εS_j) S_j`, each continuous in
`ε` at `0`. **`n` odd is what makes that true**: it gives `y_j ≠ 0` by
`Lyons.Converse.cos_two_pi_div_ne_zero`, and
`Lyons.Converse.continuousAt_signedPow` is continuity of `J_p` *away from the
origin* — at `p = 1` it genuinely fails at
`0`. The sum being finite, it passes to the limit termwise.

The limit is along `nhdsWithin 0 (Set.Ioi 0)`, i.e. `ε → 0⁺`. The
one-sided filter is not decoration: `ε < 0` is outside the range where
`Lyons.Converse.energy_testElement` holds, since the test element is positive
only for `ε ≥ 0`. -/
@[lyons_tag "lem_Ep_limit"]
theorem tendsto_energy_testElement_div {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    (hodd : Odd n) (p : ℝ) :
    Filter.Tendsto
        (fun ε : ℝ => energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) / ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-((2 / (n : ℝ)) ^ p *
          ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * (Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
              + Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))))) := by
  -- `n` odd gives `y_j ≠ 0`, which is where `J_p` is continuous.
  have hy : ∀ j : ZMod n, Real.cos (2 * π * (j.val : ℝ) / n) ≠ 0 := by
    intro j
    have h := cos_two_pi_div_ne_zero hodd (j.val : ℤ)
    rwa [show (((j.val : ℤ)) : ℝ) = (j.val : ℝ) by push_cast; ring] at h
  -- Each summand of the closed form converges as `ε → 0`.
  have hterm : ∀ (t : ZMod n → ℝ) (j : ZMod n),
      Filter.Tendsto
        (fun ε : ℝ => signedPow p (Real.cos (2 * π * (j.val : ℝ) / n) + ε * t j) * t j)
        (nhds 0) (nhds (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)) * t j)) := by
    intro t j
    refine Filter.Tendsto.mul_const _ ?_
    have hinner : Filter.Tendsto
        (fun ε : ℝ => Real.cos (2 * π * (j.val : ℝ) / n) + ε * t j)
        (nhds 0) (nhds (Real.cos (2 * π * (j.val : ℝ) / n))) := by
      have h : Filter.Tendsto (fun ε : ℝ => Real.cos (2 * π * (j.val : ℝ) / n) + ε * t j)
          (nhds 0) (nhds (Real.cos (2 * π * (j.val : ℝ) / n) + 0 * t j)) :=
        Continuous.tendsto (by fun_prop) 0
      simpa using h
    exact ((continuousAt_signedPow p (hy j)).tendsto).comp hinner
  have hsum : Filter.Tendsto
      (fun ε : ℝ => ∑ j : ZMod n,
        (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)
              + ε * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))
            * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
          + signedPow p (Real.cos (2 * π * (j.val : ℝ) / n)
              + ε * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))
            * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)))
      (nhds 0)
      (nhds (∑ j : ZMod n,
        (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
          + signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)))) :=
    tendsto_finset_sum _ fun j _ =>
      (hterm (fun i => Real.cos (2 * π * (K * (i.val : ℤ) : ℝ) / n)) j).add
        (hterm (fun i => Real.sin (2 * π * (K * (i.val : ℤ) : ℝ) / n)) j)
  have hF := (hsum.const_mul ((2 / (n : ℝ)) ^ p)).neg
  rw [show (∑ j : ZMod n,
        (signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
          + signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)))
      = ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
          * (Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
            + Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)) from
    Finset.sum_congr rfl fun _ _ => by ring] at hF
  refine Filter.Tendsto.congr' ?_ (hF.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  rw [energy_testElement hK hn hε0.le p, eq_div_iff hε0.ne']
  ring

/-! ### Positivity for small `ε` -/

/-- **The energy is positive for small `ε`.** If
`∑_{j ∈ ℤ/n} J_p(y_j) Y_j < 0` then `𝓔_p(ξ_{n,K,ε}; τ) > 0` for every
sufficiently small `ε > 0`.

This is the conclusion the whole converse direction is built for: a positive
energy is a rate perturbation along which the `ℓ^p` distance *increases*.

`Lyons.Converse.sum_signedPow_cos_mul_sin` kills the sine half, so the
hypothesis says exactly that `∑_j J_p(y_j)(Y_j + S_j) < 0`; hence the limit of
`Lyons.Converse.tendsto_energy_testElement_div` is `-(2/n)^p` times a negative
number, so positive. A quotient tending to `Θ > 0` exceeds `Θ/2` on some
`Ioo 0 ε₀`, and multiplying back by `ε > 0` gives the claim.

The conclusion is stated with `0 < ε` and `ε < ε₀` as two hypotheses rather than
as `ε ∈ Ioo 0 ε₀`; and `ε₀` is produced from the one-sided filter by
`mem_nhdsGT_iff_exists_Ioo_subset`, which is the same statement. -/
@[lyons_tag "lem_Ep_pos_small_eps"]
theorem exists_energy_testElement_pos {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    (hodd : Odd n) (p : ℝ)
    (hneg : ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
        * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n) < 0) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hκ : (0 : ℝ) < (2 / (n : ℝ)) ^ p :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) hn0) p
  -- The sine half of the sum vanishes, so the hypothesis is about `Y_j + S_j`.
  have hlt : ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
      * (Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
        + Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)) < 0 := by
    have hsplit : ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
        * (Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)
          + Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))
        = (∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))
          + ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
            * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, sum_signedPow_cos_mul_sin (n := n) p K, add_zero]
    exact hneg
  -- The limit `Θ` of the quotient is positive.
  obtain ⟨Θ, hΘ, htend⟩ : ∃ Θ : ℝ, 0 < Θ ∧ Filter.Tendsto
      (fun ε : ℝ => energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) / ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Θ) :=
    ⟨_, neg_pos.mpr (mul_neg_of_pos_of_neg hκ hlt),
      tendsto_energy_testElement_div hK hn hodd p⟩
  -- Near `0⁺` the quotient exceeds `Θ/2 > 0`.
  have hev := htend.eventually_const_lt (u := Θ / 2) (by linarith)
  obtain ⟨ε₀, hε₀, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (Filter.eventually_iff.mp hev)
  refine ⟨ε₀, hε₀, fun ε hε hεlt => ?_⟩
  have hq : Θ / 2 < energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) / ε :=
    hsub ⟨hε, hεlt⟩
  have h2 : Θ / 2 * ε
      < energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) / ε * ε :=
    mul_lt_mul_of_pos_right hq hε
  rw [div_mul_cancel₀ _ hε.ne'] at h2
  have h1 : 0 < Θ / 2 * ε := mul_pos (by linarith) hε
  linarith

end Lyons.Converse
