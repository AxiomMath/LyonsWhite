/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.InversionExtension.Blocks
import Lyons.Fourier.Inversion

/-!
# The blocks determine the element

The representation `ρ_{χ,d}` — `Lyons.InvExtBlock.rhoAlg` — sends an
element of `ℝ[G_{A,z}]` to a `2 × 2` complex matrix for each character `χ` of
`A`. This file proves that the whole family determines the element: if
`ρ_{χ,d}(x) = ρ_{χ,d}(y)` for every `χ`, then `x = y`.

This is what lets the counterexample chain identify an element by prescribing its
blocks — which is how the source introduces its test element.

## Which two entries are used, and why not the other two

`Lyons.InvExtBlock.rhoAlg_entries` gives

  `ρ_{χ,d}(y) = !![U^y(χ), χ z * V^{y,d}(χ); conj (V^{y,d}(χ)), conj (U^y(χ))]`.

The proof reads off the `(0,0)` and `(1,0)` entries. The `(0,1)` entry would do
just as well for `U` but carries the factor `χ z`, which would have to be divided
out — and `χ z` is a root of unity, so that is possible but pointless.

## Main results

* `Lyons.InvExtBlock.rhoAlg_injective` : the blocks determine the element.
-/

open Finset Matrix
open scoped ComplexConjugate

namespace Lyons.InvExtBlock

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {z : A}
  [Fact (z + z = 0)]

set_option linter.unusedDecidableInType false in
/-- **The blocks determine the element.**

If two elements of `ℝ[G_{A,z}]` have the same `2 × 2` block at every character of
`A`, they are equal.

The element `d ∈ A` is fixed and `χ` is quantified over, with `d` explicit
because nothing determines it from the conclusion. Fourier inversion
(`Lyons.AddCharFourier.dft_inversion`) recovers the two coefficient families
from their transforms, and the normal form of `Lyons.InvExt` — `rot` and `refl`
are the only constructors — turns those into all of the coefficients. The
reindexing `a ↦ a + d` is here just the instantiation `a := b - d`.

`[DecidableEq A]` does not appear in the statement's type but cannot be dropped:
it is the instance `Lyons.InvExtBlock.rhoAlg_entries` elaborates against inside
the proof, and letting `classical` supply one there makes the two disagree, so
the rewrite stops making progress. The linter that flags it is therefore disabled
for this declaration rather than worked around. -/
@[lyons_tag "lem_rho_injective"]
theorem rhoAlg_injective {x y : MonoidAlgebra ℝ (InvExt A z)} (d : A)
    (h : ∀ χ : AddChar A ℂ, rhoAlg χ d x = rhoAlg χ d y) : x = y := by
  -- The `(0,0)` entry is the abelian transform.
  have hU : ∀ χ : AddChar A ℂ,
      AddCharFourier.dft (uCoeff x) χ = AddCharFourier.dft (uCoeff y) χ := by
    intro χ
    have hent := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (h χ)
    simpa [rhoAlg_entries, Ublock] using hent
  -- The `(1,0)` entry is the conjugate of the outside transform.
  have hV : ∀ χ : AddChar A ℂ,
      AddCharFourier.dft (vCoeff x d) χ = AddCharFourier.dft (vCoeff y d) χ := by
    intro χ
    have hent := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) (h χ)
    simp only [rhoAlg_entries, Vblock, of_apply, cons_val', cons_val_zero,
      empty_val', cons_val_fin_one, cons_val_one] at hent
    exact star_injective hent
  -- Inversion turns equal transforms into equal coefficient families.
  have hu : ∀ a : A, uCoeff x a = uCoeff y a := by
    intro a
    rw [AddCharFourier.dft_inversion (uCoeff x) a,
      AddCharFourier.dft_inversion (uCoeff y) a]
    exact congrArg _ (Finset.sum_congr rfl fun χ _ => by rw [hU χ])
  have hv : ∀ a : A, vCoeff x d a = vCoeff y d a := by
    intro a
    rw [AddCharFourier.dft_inversion (vCoeff x d) a,
      AddCharFourier.dft_inversion (vCoeff y d) a]
    exact congrArg _ (Finset.sum_congr rfl fun χ _ => by rw [hV χ])
  -- The two families exhaust the coefficients, by the normal form.
  refine co_injective fun g => ?_
  cases g with
  | rot a => exact Complex.ofReal_inj.mp (hu a)
  | refl b =>
    have hb := hv (b - d)
    rw [vCoeff, vCoeff, sub_add_cancel] at hb
    exact Complex.ofReal_inj.mp hb

end Lyons.InvExtBlock
