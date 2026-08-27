/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Real

/-!
# Rate-monotonicity: the definition the three main results share

The source paper states three main theorems through **one** predicate,
`RateMonotonic G p`: the two positive results assert it, and the counterexample
*negates* it. That makes the predicate, not the three theorem statements, the
load-bearing
object — a drift in it moves the positive and negative results in opposite
directions with nothing to notice.

## Main definitions

* `Lyons.IsSymmRate` — a nonnegative, inversion-symmetric rate collection,
  quantified over **all** of `G → ℝ` rather than over `RateFn`.
* `Lyons.Generating` — the support generates `G`.
* `Lyons.distToUniform` — the `ℓ^p` distance from uniform, `d_p^λ(t)`.
* `Lyons.RateMonotonic` — the paper's rate-monotonicity.

## Where the theorems live

Only the shared vocabulary is here. Rate-monotonicity of `(D_n, 2m)` is
`Lyons.rateMonotonic_dihedral_even` in `Lyons.Objective.TheoremA`;
rate-monotonicity of every inversion extension at an even exponent is
`Lyons.rateMonotonic_invExt_even` in `Lyons.InversionExtension.Main`; its failure
away from the even integers is `Lyons.not_rateMonotonic_dihedral_of_not_even` in
`Lyons.Objective.TheoremC`.

## Why `IsSymmRate` and not `RateFn`

`RateFn` carries `atOne : toFun 1 = 0`, but the paper quantifies over every
symmetric collection in `ℝ_{≥0}^G`, placing no constraint on `λ_1`. Defining
`RateMonotonic` over `RateFn` would therefore quantify over strictly fewer
collections and state something *weaker* than the paper does. The identity rate
genuinely has no effect (`laplacian` sums over `s ≠ 1`), so the honest route is
to quantify over the paper's set and discard `λ_1` inside
`IsSymmRate.toRateFn`.
-/

namespace Lyons

open Finset

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A **symmetric rate collection**: nonnegative and invariant under
inversion, with no condition at the identity.

This is the paper's `λ ∈ ℝ_{≥0}^G` with `λ_s = λ_{s⁻¹}`. -/
@[lyons_tag "def_symm_rate"]
structure IsSymmRate (lam : G → ℝ) : Prop where
  /-- Rates are nonnegative. -/
  nonneg : ∀ g, 0 ≤ lam g
  /-- Rates are symmetric under inversion. -/
  symm : ∀ g, lam g⁻¹ = lam g

/-- Discard the identity rate, which the walk ignores, to land in `RateFn`. -/
@[lyons_tag "def_rate_discard"]
def IsSymmRate.toRateFn {lam : G → ℝ} (h : IsSymmRate lam) : RateFn G where
  toFun g := if g = 1 then 0 else lam g
  nonneg' g := by
    split
    · exact le_rfl
    · exact h.nonneg g
  symm' g := by
    by_cases hg : g = 1
    · simp [hg]
    · rw [if_neg (by simpa using hg), if_neg hg, h.symm g]
  atOne := by simp

omit [Fintype G] in
@[simp] theorem IsSymmRate.toRateFn_apply {lam : G → ℝ} (h : IsSymmRate lam) (g : G) :
    (h.toRateFn : G → ℝ) g = if g = 1 then 0 else lam g := rfl

/-- A rate collection is **generating** when its support generates `G`. -/
@[lyons_tag "def_generating"]
def Generating (lam : G → ℝ) : Prop :=
  Subgroup.closure {s : G | 0 < lam s} = ⊤

/-- The **`ℓ^p` distance to stationarity**, `d_p^λ(t)`: the `ℓ^p` distance
between the walk's time-`t` distribution and the uniform distribution. -/
@[lyons_tag "def_dist_p"]
noncomputable def distToUniform (p : ℝ) (lam : RateFn G) (t : ℝ) : ℝ :=
  (∑ g : G, |heatCoeffReal lam t g - (Fintype.card G : ℝ)⁻¹| ^ p) ^ p⁻¹

/-- **Rate-monotonicity.** The pair `(G, p)` is rate-monotonic when raising
every rate cannot increase the `ℓ^p` distance to stationarity, at any fixed
time.

This single predicate carries all three main results:
`Lyons.rateMonotonic_dihedral_even` and `Lyons.rateMonotonic_invExt_even` assert
it, `Lyons.not_rateMonotonic_dihedral_of_not_even` negates it. -/
@[lyons_tag "def_rate_monotonic"]
def RateMonotonic (G : Type*) [Group G] [Fintype G] [DecidableEq G] (p : ℝ) : Prop :=
  ∀ (lam mu : G → ℝ) (hlam : IsSymmRate lam) (hmu : IsSymmRate mu),
    Generating lam → Generating mu → (∀ s, lam s ≤ mu s) →
      ∀ t : ℝ, 0 ≤ t →
        distToUniform p hmu.toRateFn t ≤ distToUniform p hlam.toRateFn t

end Lyons
