/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Lyons.Walk.Real

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

@[expose] public section

namespace Lyons

open Finset

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
@[simp] theorem IsSymmRate.toRateFn_apply {lam : G → ℝ} (h : IsSymmRate lam) (g : G) :
    (h.toRateFn : G → ℝ) g = if g = 1 then 0 else lam g := rfl

end Lyons
