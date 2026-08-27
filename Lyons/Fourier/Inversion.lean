/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Fourier.AddCharBasic

/-!
# Fourier inversion over a finite abelian group

`Lyons.Fourier.AddCharBasic` defines the unnormalized transform
`f̂(ψ) = ∑ a, f a * ψ a` on a finite abelian group `A`, with the dual group
`AddChar A ℂ` as the frequency domain, and proves character orthogonality summed
over the dual. This file adds the **inversion formula**, which recovers `f` from
`f̂`, together with the two facts about individual character values that its
proof consumes.

## Main results

* `norm_char_apply` : `‖ψ a‖ = 1`.
* `conj_char_apply` : `conj (ψ a) = ψ (-a)`.
* `dft_inversion` : `f a = |A|⁻¹ * ∑ ψ, f̂ ψ * conj (ψ a)`.

## The two character facts

Both are Mathlib declarations — `AddChar.norm_apply` and
`AddChar.map_neg_eq_conj` — and nothing is proved for them here; they are
restated so that the inversion proof, which runs on `conj_char_apply`, and its
consumers cite them in the orientation this development uses.

## Additive versus multiplicative `A`

`A` is additive here, because the substrate is Mathlib's `AddChar A ℂ`. The
multiplicative reading `conj (χ a) = χ (a⁻¹)` of `conj_char_apply` therefore
appears below as `conj (ψ a) = ψ (-a)`.

## The transform's convention

`Lyons.AddCharFourier.dft` carries neither a conjugate nor a negation:
`dft f ψ = ∑ a, f a * ψ a`. The inversion formula therefore has the conjugate on
the character and the normalisation `|A|⁻¹` outside the sum over the dual.
-/

namespace Lyons.AddCharFourier

open Finset
open scoped ComplexConjugate

variable {A : Type*} [AddCommGroup A]

section Values

variable [Finite A]

/-- **Characters have unit modulus.**

This is Mathlib's `AddChar.norm_apply`, which is available because `A` is finite:
every element has finite order, so every character value is a root of unity. The
statement is `‖ψ a‖ = 1` rather than `|χ(a)| = 1`, since it is a character value's
*norm* that the development consumes, not the `Complex.abs` of it. -/
@[lyons_tag "lem_ext_char_abs"]
theorem norm_char_apply (ψ : AddChar A ℂ) (a : A) : ‖ψ a‖ = 1 :=
  AddChar.norm_apply ψ a

/-- **Conjugation inverts the argument**, `conj (ψ a) = ψ (-a)`.

This is Mathlib's `AddChar.map_neg_eq_conj`, oriented so as to rewrite a
conjugate into a character value; Mathlib's lemma goes the other way. Finiteness
of `A` is what makes it available: the values of a character of a finite group
are roots of unity, so `conj` and inversion agree on them, and no explicit
root-of-unity form of `ψ` is needed. Written additively, so the multiplicative
`a⁻¹` is `-a`.

`Lyons.InvExtBlock.char_neg` is the same fact in Mathlib's orientation, stated
for the fixed character of the block decomposition. -/
@[lyons_tag "lem_ext_char_conj"]
theorem conj_char_apply (ψ : AddChar A ℂ) (a : A) : conj (ψ a) = ψ (-a) :=
  (AddChar.map_neg_eq_conj ψ a).symm

end Values

variable [Fintype A]

/-- **Fourier inversion.** Every `f : A → ℂ` is recovered from its transform by
averaging against the conjugate characters,
`f a = |A|⁻¹ * ∑ ψ, f̂ ψ * conj (ψ a)`.

The proof expands `dft`, uses `conj_char_apply` and multiplicativity to combine
`ψ a' * conj (ψ a)` into `ψ (a' - a)`, exchanges the two finite sums, and
collapses the inner sum over the dual with `sum_char_apply`. Only `a' = a`
survives, contributing `|A| * f a`; `|A| ≠ 0` because `A` is nonempty.

`DecidableEq A` is not assumed: it appears only inside the proof, where
`sum_char_apply`'s `if` needs it, and is supplied there by `classical`. -/
@[lyons_tag "lem_dft_inversion"]
theorem dft_inversion (f : A → ℂ) (a : A) :
    f a = (Fintype.card A : ℂ)⁻¹ * ∑ ψ : AddChar A ℂ, dft f ψ * conj (ψ a) := by
  classical
  have hcard : (Fintype.card A : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨a⟩).ne'
  -- A single term of the sum over the dual, with the character at a difference.
  have expand : ∀ ψ : AddChar A ℂ, dft f ψ * conj (ψ a) = ∑ a' : A, f a' * ψ (a' - a) := by
    intro ψ
    rw [dft_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a' _ ↦ ?_
    rw [conj_char_apply, mul_assoc, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg]
  -- Orthogonality collapses the inner sum over the dual.
  have step : ∀ a' : A, ∑ ψ : AddChar A ℂ, f a' * ψ (a' - a)
      = f a' * if a' - a = 0 then (Fintype.card A : ℂ) else 0 := by
    intro a'
    rw [← Finset.mul_sum, sum_char_apply]
  have key : ∑ ψ : AddChar A ℂ, dft f ψ * conj (ψ a) = (Fintype.card A : ℂ) * f a := by
    rw [Finset.sum_congr rfl fun ψ _ ↦ expand ψ, Finset.sum_comm,
      Finset.sum_congr rfl fun a' _ ↦ step a', Finset.sum_eq_single a]
    · rw [sub_self, if_pos rfl, mul_comm]
    · intro b _ hb
      rw [if_neg (by simpa [sub_eq_zero] using hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [key, inv_mul_cancel_left₀ hcard]

end Lyons.AddCharFourier
