/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Fourier.AddCharBasic

/-!
# Even parts over an arbitrary finite abelian group

`Lyons.Fourier.EvenPart` develops the even part of a function on `ZMod N` and the
three facts about it that the reflection inequality consumes.
`Lyons.rateMonotonic_invExt_even` needs the same three facts over an arbitrary
finite abelian group `A`, with the dual `AddChar A ℂ` as the frequency domain;
this file supplies them, on top of `Lyons.AddCharFourier.dft`.

## Main definitions

* `Lyons.AddCharFourier.evenPart` : `f^ev a = (f a + f (-a)) / 2`.

## Main results

* `Lyons.AddCharFourier.dft_injective` : the transform determines the function.
* `Lyons.AddCharFourier.dft_evenPart` : the transform of the even part is the
  real part of the transform.
* `Lyons.AddCharFourier.evenPart_eq_of_re_dft_eq` : hence equal real parts force
  equal even parts.
* `Lyons.AddCharFourier.sum_mul_evenPart` : an even weight cannot see the odd
  part of the function it is paired against.

## Relation to the cyclic development

The cyclic proofs port almost verbatim. Two steps differ.

Injectivity is *not* obtained from an inversion formula: the cyclic proof uses
Mathlib's `ZMod.dft_dft`, which has no general-`A` counterpart here. Parseval
does the same work — `sum_norm_sq_dft` turns a vanishing transform into a
vanishing sum of squared norms, and a sum of nonnegative reals vanishes only
termwise. Fourier inversion would give the same conclusion, but Parseval is the
shorter route to it and is already available.

Negating the frequency is done by reindexing the *group* variable by `a ↦ -a`
and using `AddChar.map_neg_eq_conj`, rather than by the explicit root-of-unity
form of `ZMod.stdAddChar` that the cyclic proof reads `conj (stdAddChar x)` off.
-/

open Finset
open scoped ComplexConjugate

namespace Lyons.AddCharFourier

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- The **even part** of a function on a finite abelian group. The general-`A`
form of `ZMod.evenPart`.

Stated for `ℂ`-valued functions rather than real-valued ones: the coefficient
functions this is applied to arise as matrix entries, hence are `ℂ`-valued, and
nothing in the argument uses realness. -/
noncomputable def evenPart (f : A → ℂ) : A → ℂ :=
  fun a => (f a + f (-a)) / 2

omit [Fintype A] [DecidableEq A] in
@[simp] theorem evenPart_apply (f : A → ℂ) (a : A) :
    evenPart f a = (f a + f (-a)) / 2 := rfl

/-! ### The transform determines the function -/

omit [DecidableEq A] in
theorem dft_sub (f g : A → ℂ) (χ : AddChar A ℂ) :
    dft (f - g) χ = dft f χ - dft g χ := by
  classical
  simp only [dft_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq A] in
/-- **The transform determines the function.** By Parseval a function whose
transform vanishes has vanishing `ℓ²` norm, and a sum of nonnegative reals
vanishes only termwise. -/
theorem dft_injective :
    Function.Injective (dft : (A → ℂ) → AddChar A ℂ → ℂ) := by
  classical
  intro f h hfh
  have hzero : ∀ χ : AddChar A ℂ, dft (f - h) χ = 0 := fun χ => by
    rw [dft_sub, congrFun hfh χ, sub_self]
  have hsum : ∑ a : A, ‖(f - h) a‖ ^ 2 = 0 := by
    rw [sum_norm_sq_dft]
    simp [hzero]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => by positivity).mp hsum
  funext a
  have ha := hterm a (Finset.mem_univ a)
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, Pi.sub_apply, sub_eq_zero] at ha
  exact ha

/-! ### The even part through the transform -/

omit [DecidableEq A] in
/-- **The transform of the even part is the real part of the transform.** The
general-`A` form of `ZMod.dft_evenPart`. -/
theorem dft_evenPart {f : A → ℂ} (hf : ∀ a, conj (f a) = f a) (χ : AddChar A ℂ) :
    dft (evenPart f) χ = (((dft f χ).re : ℝ) : ℂ) := by
  classical
  -- Reindexing the group variable by negation conjugates the transform.
  have hconj : ∑ a : A, f (-a) * χ a = conj (dft f χ) := by
    rw [dft_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.neg A) _ _ fun a ↦ ?_
    rw [map_mul, hf, ← AddChar.map_neg_eq_conj]
    simp
  have hsplit : dft (evenPart f) χ = (dft f χ + ∑ a : A, f (-a) * χ a) / 2 := by
    rw [dft_apply, dft_apply, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [evenPart_apply]; ring
  rw [hsplit, hconj, Complex.add_conj]
  push_cast
  ring

omit [DecidableEq A] in
/-- **Equal real parts of the transforms means equal even parts.** The
general-`A` form of `ZMod.evenPart_eq_of_re_dft_eq`. -/
theorem evenPart_eq_of_re_dft_eq {f h : A → ℂ}
    (hfr : ∀ a, conj (f a) = f a) (hhr : ∀ a, conj (h a) = h a)
    (hre : ∀ χ : AddChar A ℂ, (dft f χ).re = (dft h χ).re) :
    evenPart f = evenPart h :=
  dft_injective (funext fun χ => by
    rw [dft_evenPart hfr, dft_evenPart hhr, hre])

omit [DecidableEq A] in
/-- Pairing an **even** weight against a function sees only its even part. The
general-`A` form of `ZMod.sum_mul_evenPart`. -/
theorem sum_mul_evenPart (φ ψ : A → ℂ) (hφ : ∀ a, φ (-a) = φ a) :
    ∑ a : A, φ a * ψ a = ∑ a : A, φ a * evenPart ψ a := by
  have hhalf : ∑ a : A, φ a * evenPart ψ a
      = (∑ a : A, φ a * ψ a) / 2 + (∑ a : A, φ a * ψ (-a)) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [evenPart_apply]; ring
  -- Reindexing by negation moves the negation from `ψ` onto `φ`, where the
  -- evenness hypothesis removes it.
  have hneg : ∑ a : A, φ a * ψ (-a) = ∑ a : A, φ a * ψ a :=
    Fintype.sum_equiv (Equiv.neg A) _ _ fun a ↦ by
      simp only [Equiv.neg_apply]
      rw [hφ a]
  rw [hhalf, hneg]
  ring

end Lyons.AddCharFourier
