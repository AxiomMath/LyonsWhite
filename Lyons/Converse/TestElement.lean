/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lyons.GroupAlgebra.Basic
import Lyons.InversionExtension.Basic

/-!
# The test element of the converse direction

The element `ξ_{n,K,ε}` of `ℝ[G_{C,1}]` at which rate-monotonicity is shown to
fail, together with its coefficients and its self-adjointness.

## Main definitions

* `Lyons.Converse.testElement` : the test element `ξ_{n,K,ε}`.

## Main results

* `Lyons.Converse.co_testElement_rot` : the abelian coefficient `u^ξ(c^j)`.
* `Lyons.Converse.co_testElement_refl` : the outside coefficient `v^{ξ,1}(c^j)`.
* `Lyons.Converse.invol_testElement` : `ξ^* = ξ`.

## Implementation notes

Three standing conventions of this development govern the statements below.

*The cyclic group is `ZMod n`, written additively.*  Rather than an abstract
cyclic `C` of order `n` with a generator `c` and `c^j` for `j ∈ ℤ/n`, here
`C = ZMod n` with `c = 1`, so `c^j` is the residue `j` itself and the indexing
bijection is the identity.  Fixing the model costs no generality —
`Lyons.Converse.cyclicIndex_bijective` transports everything below to any cyclic
group of order `n` — and it is what lets the group be named as a type, which a
definition must do.

*`z = 1` is written `z = 0`.*  The group `G_{C,1}` is `InvExt (ZMod n) 0`, the
inversion extension at the neutral element of the additively written `C`.  The
extension's standing hypothesis `z² = 1` is then
`Lyons.InvExt.instFactZModZeroAddZero`.  Under the dictionary of
`Lyons.InversionExtension.Basic`, `ι(c^j)` is `InvExt.rot j`, `τ` is
`InvExt.b = InvExt.refl 0`, and `ι(c^j)τ` is `InvExt.refl j`.

*The angle `2πj/n` is read at the `ZMod.val` lift.*  For a residue `j ∈ ℤ/n`
the value `cos(2πj/n)` is defined by lifting `j` to an integer, and is
independent of the lift.  This file fixes the lift to `ZMod.val`, which is the
convention of `Lyons.Converse.TrigSums` and of `Lyons.Converse.omegaN`, so
that the trigonometric sums proved there apply to these coefficients verbatim.
Independence of the lift is not a hypothesis but a lemma, and the one place it
is needed — negating the index in `invol_testElement` — is
`cos_two_pi_div_neg_residue` below.

Nothing below uses `ε ≥ 0`, so no sign hypothesis on `ε` is assumed.
-/

namespace Lyons.Converse

open Finset Real

/-! ### The angle at a residue

`Real.cos (2 * π * m / n)` for `m : ℤ` factors through the residue of `m`, which
means that `cos(2πj/n)` is well defined for `j ∈ ℤ/n`.  The same remark appears
as a private helper in `Lyons.Converse.TrigSums`; it is repeated rather than
shared because there it is private, and it is stated here in the negated form
that is the only form this file consumes. -/

/-- The angle `2πm/n` depends on the integer `m` only through its residue mod
`n`, as far as the cosine can see. -/
private theorem cos_two_pi_div_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ}
    (h : (a : ZMod n) = (b : ZMod n)) :
    Real.cos (2 * π * a / n) = Real.cos (2 * π * b / n) := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).mp h.symm
  have hab : (a : ℝ) = (b : ℝ) + (n : ℝ) * (q : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hq
    push_cast at this
    linarith
  rw [show 2 * π * (a : ℝ) / n = 2 * π * (b : ℝ) / n + (q : ℝ) * (2 * π) by
        rw [hab]; field_simp,
    Real.cos_add_int_mul_two_pi]

/-- **The cosine of the angle is even in the residue.**  If `a` and `-b` have
the same residue mod `n` then `cos(2πa/n) = cos(2πb/n)`: the value depends only
on the residue, and the cosine is even. -/
private theorem cos_two_pi_div_neg_residue {n : ℕ} (hn : n ≠ 0) {a b : ℤ}
    (h : (a : ZMod n) = -(b : ZMod n)) :
    Real.cos (2 * π * a / n) = Real.cos (2 * π * b / n) := by
  rw [cos_two_pi_div_congr hn (b := -b) (by push_cast; exact h),
    show 2 * π * ((-b : ℤ) : ℝ) / n = -(2 * π * (b : ℝ) / n) by push_cast; ring,
    Real.cos_neg]

variable {n : ℕ} [NeZero n]

/-- `cos(2πj/n)` is even in `j ∈ ℤ/n`, at the `ZMod.val` lift.  Stated in the
coercion shape the test element is written in, so that it rewrites there. -/
private theorem cos_two_pi_val_neg (j : ZMod n) :
    Real.cos (2 * π * ((-j).val : ℝ) / n) = Real.cos (2 * π * (j.val : ℝ) / n) := by
  rw [show ((-j).val : ℝ) = (((-j).val : ℤ) : ℝ) by push_cast; ring,
    show ((j.val : ℕ) : ℝ) = ((j.val : ℤ) : ℝ) by push_cast; ring]
  exact cos_two_pi_div_neg_residue (NeZero.ne n) (by push_cast [ZMod.natCast_zmod_val]; ring)

/-- `cos(2πKj/n)` is even in `j ∈ ℤ/n`, in the coercion shape of the test
element.  The companion of `cos_two_pi_val_neg` with a multiplier. -/
private theorem cos_two_pi_mul_val_neg (K : ℤ) (j : ZMod n) :
    Real.cos (2 * π * (K * ((-j).val : ℤ) : ℝ) / n)
      = Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n) := by
  rw [show (K * ((-j).val : ℤ) : ℝ) = ((K * ((-j).val : ℤ) : ℤ) : ℝ) by push_cast; ring,
    show (K * (j.val : ℤ) : ℝ) = ((K * (j.val : ℤ) : ℤ) : ℝ) by push_cast; ring]
  exact cos_two_pi_div_neg_residue (NeZero.ne n) (by push_cast [ZMod.natCast_zmod_val]; ring)

/-! ### The test element -/

/-- **The test element**
`ξ_{n,K,ε} = ∑_j (2/n)(cos(2πj/n) + ε cos(2πKj/n)) ι(c^j)`
`             + ∑_j (2/n)(cos(2πj/n) + ε sin(2πKj/n)) ι(c^j)τ`
of `ℝ[G_{C,1}]`.

Here `C`, `c` and `z = 1` are the additive `ZMod n`, its generator `1`, and
`z = 0`; the angles are read at the `ZMod.val` lift; and `ε` is not required to
be nonnegative.  See the module notes for all three.

The element is naturally described by prescribing its Fourier data and then
inverting.  But "the element whose blocks are the following matrices" is an
existence claim rather than a definition, so the element is introduced here by
its coefficients — a single defining expression with no claim attached — and the
Fourier data becomes the content of a lemma. -/
@[lyons_tag "def_x_eps"]
noncomputable def testElement (n : ℕ) [NeZero n] (K : ℤ) (ε : ℝ) :
    MonoidAlgebra ℝ (InvExt (ZMod n) 0) :=
  (∑ j : ZMod n, MonoidAlgebra.single (.rot j)
      (2 / n * (Real.cos (2 * π * (j.val : ℝ) / n)
        + ε * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))))
    + ∑ j : ZMod n, MonoidAlgebra.single (.refl j)
      (2 / n * (Real.cos (2 * π * (j.val : ℝ) / n)
        + ε * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)))

/-- **The abelian coefficients of the test element**,
`u^{ξ_{n,K,ε}}(c^j) = (2/n)(cos(2πj/n) + ε cos(2πKj/n))`.

Stated on `Lyons.co` at `InvExt.rot j`, which is `ι(c^j)`; the coefficient `u^x`
is `Lyons.uCoeff`, and `Lyons.uCoeff x a = co x (.rot a)` after
complexification, so this is that value.

Exactly one summand of `testElement` contributes: the two constructors of
`InvExt` are disjoint and injective, which is the concrete model's form of the
normal form of an inversion extension. -/
@[lyons_tag "lem_x_eps_rot_coeff"]
theorem co_testElement_rot (K : ℤ) (ε : ℝ) (j : ZMod n) :
    co (testElement n K ε) (.rot j)
      = 2 / n * (Real.cos (2 * π * (j.val : ℝ) / n)
          + ε * Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n)) := by
  simp [testElement, co_sum]

/-- **The outside coefficients of the test element**,
`v^{ξ_{n,K,ε},1}(c^j) = (2/n)(cos(2πj/n) + ε sin(2πKj/n))`.

This is stated at the outside index `d = 1`, the neutral element of `C`, which
additively is `d = 0`.  Since `Lyons.vCoeff x d a = co x (.refl (a + d))`, at
`d = 0` the value `v^{ξ,1}(c^j)` is `co ξ (.refl j)`, which is what is stated
here — on `co` rather than on `vCoeff`, so that no complexification
intervenes.

Taking `d` to be the neutral element is a genuine restriction of the general
setting, available because `z = 0` makes the inverse orbit of `τ` a singleton,
so one outside element suffices.  The proof is that of
`co_testElement_rot`, with the second sum contributing instead of the first. -/
@[lyons_tag "lem_x_eps_refl_coeff"]
theorem co_testElement_refl (K : ℤ) (ε : ℝ) (j : ZMod n) :
    co (testElement n K ε) (.refl j)
      = 2 / n * (Real.cos (2 * π * (j.val : ℝ) / n)
          + ε * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n)) := by
  simp [testElement, co_sum]

/-- **The test element is self-adjoint**, `(ξ_{n,K,ε})^* = ξ_{n,K,ε}`.

By `Lyons.co_invol` the claim is that `ξ_{g⁻¹} = ξ_g` for every `g`, and there
are two cases.  For `g = ι(c^j)` we have `g⁻¹ = ι(c^{-j})`, and both cosines in
`co_testElement_rot` are even in `j`, so the two coefficients agree.

For `g = ι(c^j)τ` we have `g⁻¹ = ι(z c^j)τ`, and **this is where `z = 0` does
the work**: with `z` trivial, `g⁻¹ = g`, so the two outside coefficients are
literally the same number and the outside half of `testElement` carries no
condition at all.  For a nontrivial `z` the condition
`Lyons.vCoeff_involution_add` imposes in general is `v^{x,d}(za) = v^{x,d}(a)`,
and nothing in the outside half of `testElement` would satisfy it: the sine there
is odd in `j`, not invariant under a translation of order two. -/
@[lyons_tag "lem_x_eps_selfadjoint"]
theorem invol_testElement (K : ℤ) (ε : ℝ) :
    invol (testElement n K ε) = testElement n K ε := by
  refine co_injective fun g ↦ ?_
  rw [co_invol]
  cases g with
  | rot j =>
    rw [InvExt.inv_rot, co_testElement_rot, co_testElement_rot, cos_two_pi_val_neg,
      cos_two_pi_mul_val_neg]
  | refl j => rw [InvExt.inv_refl, add_zero]

end Lyons.Converse
