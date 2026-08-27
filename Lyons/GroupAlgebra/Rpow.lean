/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Matrix.Order
import Lyons.GroupAlgebra.Commutant

/-!
# Fractional powers of positive elements of the group algebra

Fractional powers are taken on the operator side, in `Matrix G G ℂ`, via the
continuous functional calculus. `Lyons.cfc_L_conv` already shows the result is
again a left convolution, so the coefficient function of `x ^ θ` can be read off
the first column without ever constructing a group-algebra element — which is
what the downstream sections actually consume.

## The scope is load-bearing

The Loewner order on matrices is `scoped[MatrixOrder]`
(`Mathlib.Analysis.Matrix.Order`), so `open scoped MatrixOrder ComplexOrder`
is required before `Matrix G G ℂ` has a `PartialOrder`, hence before
`CFC.rpow` applies or `M ^ (θ : ℝ)` elaborates at all. Unscoped, even
`HPow (Matrix G G ℂ) ℝ` fails to synthesize, while the underlying `cfc` keeps
working — so the omission is silent until instantiation.

## Main results

* `Lyons.mrpow_nonneg` : `0 ≤ (L x) ^ θ`, with no hypothesis needed.
* `Lyons.mrpow_add` : `(L x) ^ (θ + θ') = (L x) ^ θ * (L x) ^ θ'` for
  `θ, θ' > 0`, with no invertibility hypothesis.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- Positivity of `L x` in the Loewner order is exactly `IsPos x`. -/
theorem isPos_iff_le (x : MonoidAlgebra ℝ G) : IsPos x ↔ 0 ≤ L x :=
  Matrix.nonneg_iff_posSemidef.symm

-- `DecidableEq G` is needed for the `Matrix G G ℂ` ring structure that these
-- statements are about, but Lean sees it used only inside the proof terms. The
-- linter's suggested fix (`open scoped Classical`) would swap in a different
-- decidability instance from the one the surrounding section uses, risking
-- instance mismatch against `Lyons.L`; keeping the section variable is correct
-- here, so the check is disabled for these two declarations only.
set_option linter.unusedDecidableInType false in
/-- Fractional powers are positive, at `L x` and with **no** hypothesis on it:
Mathlib's `CFC.nnrpow_nonneg` needs none, because `nnrpow` is built from `cfcₙ`,
which preserves the nonnegativity predicate unconditionally. The usual `M ⪰ 0`
premise is therefore unnecessary here and is not assumed. -/
theorem mrpow_nonneg (x : MonoidAlgebra ℝ G) (θ : NNReal) :
    (0 : Matrix G G ℂ) ≤ (L x) ^ θ :=
  CFC.nnrpow_nonneg

set_option linter.unusedDecidableInType false in
/-- Fractional powers add, for strictly positive exponents and with **no**
invertibility hypothesis.

`CFC.rpow_add` would need `IsUnit`, which fails for the centered heat element;
`CFC.nnrpow_add` needs only `0 < θ` and `0 < θ'`. -/
@[lyons_tag "lem_algebra_rpow_add"]
theorem mrpow_add (x : MonoidAlgebra ℝ G) {θ θ' : NNReal}
    (hθ : 0 < θ) (hθ' : 0 < θ') :
    (L x) ^ (θ + θ') = (L x) ^ θ * (L x) ^ θ' :=
  CFC.nnrpow_add hθ hθ'

end Lyons
