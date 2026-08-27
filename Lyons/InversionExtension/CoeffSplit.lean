/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.GroupAlgebra.Basic
import Lyons.InversionExtension.Basic

/-!
# Paired coefficient sums over an inversion extension

A sum over the inversion extension `G_{A,z}` — `Lyons.InvExt` — splits along the
normal form into an abelian half, indexed by `ι a = InvExt.rot a`, and an outside
half, indexed by
`ι (a + d) * τ = InvExt.refl (a + d)` for a chosen `d : A`. This file records
that split for a summand depending on the coefficients of **two** group-algebra
elements at once.

## Main results

* `Lyons.sum_invExt` : the split for an arbitrary summand.
* `Lyons.sum_coeff_split_pair` : the split for a summand built from the
  coefficients of two elements.

## Why the two-element version is needed

`Lyons.sum_coeff_split` is the one-element analogue, and this file follows it
closely: the same reindexing, and the same
generalisation of the codomain from the source's `ℝ` to an arbitrary
`AddCommMonoid M`. It cannot be reused here,
because the sums it is applied to pair the coefficients of an element against
those of a *different* element — its reflection sandwich — and a single-argument
`Ψ` cannot see both.

## Real coefficients, and the correspondence with the block transforms

The two summands below are the `uCoeff`/`vCoeff` shapes of the block
representations:
`Lyons.InvExtBlock.uCoeff x a = (co x (.rot a) : ℂ)` and
`Lyons.InvExtBlock.vCoeff x d a = (co x (.refl (a + d)) : ℂ)`. Those two are
`ℂ`-valued, because they arise as entries of the two-dimensional
representations; the statement here is on the real coefficients `Lyons.co`,
which is where the source states it — its `Ψ` takes real arguments — and the
complex forms are its coercion. Staying on `co` also keeps this file independent
of the representation layer.

## A hypothesis the source carries and this file does not

The source assumes `z² = 1`, that is `Fact (z + z = 0)`, throughout its
treatment of `G_{A,z}`, since that is what makes `G_{A,z}` a group. The split
below is a pure reindexing of the finite carrier `InvExt A z`, which is defined
for every `z`, so the hypothesis is not assumed; every consumer has it in scope
in any case. This is the same economy as in `Lyons.sum_coeff_split`, which does
not assume `Ψ 0 = 0` because the sums are taken over the whole index type rather
than over supports.
-/

open Finset

namespace Lyons

variable {A : Type*} [AddCommGroup A] [Fintype A] {z : A}

/-- **Splitting a sum over `G_{A,z}` along the normal form.** The abelian half
is indexed by `ι a = InvExt.rot a` and the outside half by
`ι (a + d) * τ = InvExt.refl (a + d)`, for an arbitrary `d : A`.

This is `InvExt.sumEquiv` composed on the outside half with the translation
`Equiv.addRight d` of `A`; the composite is a bijection `A ⊕ A ≃ G_{A,z}`, and
the statement is `Fintype.sum_sum_type` after reindexing along it. The analogue
of `Lyons.sum_dihedral`, with the extra translation that the one-element split
also inserts. -/
theorem sum_invExt {M : Type*} [AddCommMonoid M] (d : A) (F : InvExt A z → M) :
    ∑ g : InvExt A z, F g
      = (∑ a : A, F (.rot a)) + ∑ a : A, F (.refl (a + d)) := by
  rw [← Equiv.sum_comp
      ((Equiv.sumCongr (Equiv.refl A) (Equiv.addRight d)).trans InvExt.sumEquiv) F,
    Fintype.sum_sum_type]
  rfl

/-- **Paired coefficient sums split along the normal form.** For
`x, y ∈ ℝ[G_{A,z}]`, an element `d ∈ A` and a summand `Ψ` of two real
arguments,

`∑_{g ∈ G} Ψ (x_g) (y_g) = ∑_{a ∈ A} Ψ (u^x a) (u^y a) + ∑_{a ∈ A} Ψ (v^{x,d} a) (v^{y,d} a)`.

Two deviations from the source, both recorded in the module docstring: the
codomain of `Ψ` is an arbitrary `AddCommMonoid` rather than `ℝ`, generalizing as
`Lyons.sum_coeff_split` does, and `Ψ` is curried rather than a function on
`ℝ × ℝ`. The source's `u^x(a)` and `v^{x,d}(a)` are `co x (.rot a)` and
`co x (.refl (a + d))`, the real forms of `Lyons.InvExtBlock.uCoeff` and
`Lyons.InvExtBlock.vCoeff`. -/
@[lyons_tag "lem_coeff_split_pair"]
theorem sum_coeff_split_pair {M : Type*} [AddCommMonoid M]
    (x y : MonoidAlgebra ℝ (InvExt A z)) (d : A) (Ψ : ℝ → ℝ → M) :
    ∑ g : InvExt A z, Ψ (co x g) (co y g)
      = (∑ a : A, Ψ (co x (.rot a)) (co y (.rot a)))
        + ∑ a : A, Ψ (co x (.refl (a + d))) (co y (.refl (a + d))) :=
  sum_invExt d fun g ↦ Ψ (co x g) (co y g)

end Lyons
