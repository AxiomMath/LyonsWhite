/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.BlockPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The block powers are continuous in the block data

The entries of `ρ_{χ,d}(𝓢_{x,θ,τ})` have to vary continuously with the
regularisation parameter `ς`. By `Lyons.rhoAlg_sandwich` each entry is a fixed
polynomial in the four block powers `Lyons.bpAlpha`, `Lyons.bpBeta`,
`Lyons.bpGamma` and `Lyons.bpDelta`, so it is enough that those four are
continuous in the pair `(U, w)`.

## The positivity hypothesis is not needed

One route argues that `U ≥ w ≥ 0` makes both eigenvalues `μ_± = U ± w`
nonnegative, and then that `μ ↦ μ^s` is continuous on `[0, ∞)` with `μ = 0` the
delicate point.

That detour is avoidable. `Continuous.rpow_const` asks only `∀ x, f x ≠ 0 ∨ 0 ≤ p`,
and `0 ≤ p` discharges it *uniformly* — `fun t : ℝ => t ^ p` is continuous on all
of `ℝ` for `p ≥ 0`, negative base included, because `Real.rpow` at a negative
base is `|t| ^ p * cos (π p)`, which is continuous in `t`, and at `t = 0` with
`p > 0` the value is `0`. So no sign information about `U ± w` is required here,
and the lemmas below carry none.

This is a strengthening, not a shortcut: the consumer may still have `U ≥ w ≥ 0`
available, but it no longer has to thread it through the continuity step.

## Main results

* `Lyons.continuous_bpAlpha`, `..._bpBeta`, `..._bpGamma`, `..._bpDelta` —
  continuity in `(U, w)` for a fixed exponent.
-/

namespace Lyons

variable {θ : ℝ}

/-- `fun p : ℝ × ℝ => (p.1 + p.2) ^ s` is continuous for `0 ≤ s`. The shared
core of the four statements below. -/
private theorem continuous_add_rpow {s : ℝ} (hs : 0 ≤ s) :
    Continuous fun p : ℝ × ℝ => (p.1 + p.2) ^ s :=
  (continuous_fst.add continuous_snd).rpow_const fun _ => Or.inr hs

/-- `fun p : ℝ × ℝ => (p.1 - p.2) ^ s` is continuous for `0 ≤ s`. -/
private theorem continuous_sub_rpow {s : ℝ} (hs : 0 ≤ s) :
    Continuous fun p : ℝ × ℝ => (p.1 - p.2) ^ s :=
  (continuous_fst.sub continuous_snd).rpow_const fun _ => Or.inr hs

/-- **`α` is continuous in the block data.** No sign hypothesis on `U` or `w`;
see the module docstring. -/
theorem continuous_bpAlpha (hθ : 0 ≤ θ) :
    Continuous fun p : ℝ × ℝ => bpAlpha p.1 p.2 θ :=
  ((continuous_add_rpow hθ).add (continuous_sub_rpow hθ)).div_const 2

/-- **`β` is continuous in the block data.** -/
theorem continuous_bpBeta (hθ : 0 ≤ θ) :
    Continuous fun p : ℝ × ℝ => bpBeta p.1 p.2 θ :=
  ((continuous_add_rpow hθ).sub (continuous_sub_rpow hθ)).div_const 2

/-- **`γ` is continuous in the block data.** The exponent is `1 - θ`, so the
hypothesis is `θ ≤ 1`. -/
theorem continuous_bpGamma (hθ' : θ ≤ 1) :
    Continuous fun p : ℝ × ℝ => bpGamma p.1 p.2 θ :=
  ((continuous_add_rpow (by linarith : (0:ℝ) ≤ 1 - θ)).add
    (continuous_sub_rpow (by linarith : (0:ℝ) ≤ 1 - θ))).div_const 2

/-- **`δ` is continuous in the block data.** -/
theorem continuous_bpDelta (hθ' : θ ≤ 1) :
    Continuous fun p : ℝ × ℝ => bpDelta p.1 p.2 θ :=
  ((continuous_add_rpow (by linarith : (0:ℝ) ≤ 1 - θ)).sub
    (continuous_sub_rpow (by linarith : (0:ℝ) ≤ 1 - θ))).div_const 2

/-! ### Continuity in the exponent, on the open interval

The four powers are also continuous in `θ` with the block data held fixed, which
is what shows the energy integrand to be measurable. Unlike continuity in the
data, this is **not** global: the open interval is essential, and not for
convenience.

`bpAlpha` carries `(U - w) ^ θ`, and `U - w` is genuinely `0` in this
development — at the trivial character the regularised element has
`U = w = ς/2` exactly, so `U - w = 0` for every `ς`. Since `Real.rpow` sets
`0 ^ 0 = 1` while `0 ^ θ = 0` for `θ ≠ 0`, the function `θ ↦ (U - w) ^ θ` jumps
at `θ = 0`; `bpGamma` and `bpDelta`, whose exponent is `1 - θ`, jump at `θ = 1`
for the same reason. Both endpoints are therefore real discontinuities and not
artefacts of the statement.

That costs nothing downstream: the energy integrates over an interval, the two
endpoints are a null set, and `Lyons.tendsto_intervalIntegral_of_dominated`
already asks only for almost-everywhere hypotheses on `Set.Ioo`. -/

/-- The shared core: `θ ↦ b ^ e θ` is continuous at `θ` as soon as the exponent
`e θ` is strictly positive there, whatever the sign of the base. This is
`Real.ContinuousAt.rpow` with the `f x ≠ 0` disjunct declined — declining it is
the whole point, since the base really can vanish. -/
private theorem continuousAt_const_rpow {b : ℝ} {e : ℝ → ℝ} {θ : ℝ}
    (he : ContinuousAt e θ) (hpos : 0 < e θ) :
    ContinuousAt (fun t : ℝ => b ^ e t) θ :=
  ContinuousAt.rpow continuousAt_const he (Or.inr hpos)

/-- **`α` is continuous in `θ` on `(0, 1)`.** -/
theorem continuousOn_bpAlpha_exponent (U w : ℝ) :
    ContinuousOn (fun t : ℝ => bpAlpha U w t) (Set.Ioo 0 1) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt ?_
  unfold bpAlpha
  exact ((continuousAt_const_rpow (b := U + w) continuousAt_id hθ.1).add
    (continuousAt_const_rpow (b := U - w) continuousAt_id hθ.1)).div_const 2

/-- **`β` is continuous in `θ` on `(0, 1)`.** -/
theorem continuousOn_bpBeta_exponent (U w : ℝ) :
    ContinuousOn (fun t : ℝ => bpBeta U w t) (Set.Ioo 0 1) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt ?_
  unfold bpBeta
  exact ((continuousAt_const_rpow (b := U + w) continuousAt_id hθ.1).sub
    (continuousAt_const_rpow (b := U - w) continuousAt_id hθ.1)).div_const 2

/-- **`γ` is continuous in `θ` on `(0, 1)`.** The exponent is `1 - θ`, positive
exactly because `θ < 1`. -/
theorem continuousOn_bpGamma_exponent (U w : ℝ) :
    ContinuousOn (fun t : ℝ => bpGamma U w t) (Set.Ioo 0 1) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt ?_
  have hsub : ContinuousAt (fun t : ℝ => 1 - t) θ := by fun_prop
  have hpos : (0 : ℝ) < 1 - θ := by have := hθ.2; linarith
  unfold bpGamma
  exact ((continuousAt_const_rpow (b := U + w) hsub hpos).add
    (continuousAt_const_rpow (b := U - w) hsub hpos)).div_const 2

/-- **`δ` is continuous in `θ` on `(0, 1)`.** -/
theorem continuousOn_bpDelta_exponent (U w : ℝ) :
    ContinuousOn (fun t : ℝ => bpDelta U w t) (Set.Ioo 0 1) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt ?_
  have hsub : ContinuousAt (fun t : ℝ => 1 - t) θ := by fun_prop
  have hpos : (0 : ℝ) < 1 - θ := by have := hθ.2; linarith
  unfold bpDelta
  exact ((continuousAt_const_rpow (b := U + w) hsub hpos).sub
    (continuousAt_const_rpow (b := U - w) hsub hpos)).div_const 2

end Lyons
