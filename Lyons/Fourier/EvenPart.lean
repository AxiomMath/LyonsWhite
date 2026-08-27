/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Fourier.Majorant

/-!
# Even parts and counting norms on `ZMod N`

## Main definitions

* `ZMod.evenPart` : `f^ev j = (f j + f (-j)) / 2`.
* `ZMod.countNorm` : the counting `ℓ^p` norm `(∑ j, ‖f j‖ ^ p) ^ (1/p)`.

## Main results

* `ZMod.dft_neg_of_even`, `ZMod.dft_neg_of_real` : negating the frequency.
* `ZMod.dft_injective` : the transform determines the function.
* `ZMod.dft_evenPart` : the transform of the even part is the real part of the
  transform.
* `ZMod.evenPart_eq_of_re_dft_eq` : hence equal real parts force equal even parts.
* `ZMod.sum_mul_evenPart` : an even weight cannot see the odd part of `ψ`.
-/

open Finset AddChar
open scoped ComplexConjugate

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The **even part** of a function on `ZMod N`.

Stated for `ℂ`-valued functions rather than real-valued ones: the coefficient
functions this is applied to arise as matrix entries, hence are `ℂ`-valued, and
nothing in the argument uses realness. -/
@[lyons_tag "def_even_part"]
noncomputable def evenPart (f : ZMod N → ℂ) : ZMod N → ℂ :=
  fun j => (f j + f (-j)) / 2

omit [NeZero N] in
@[simp] theorem evenPart_apply (f : ZMod N → ℂ) (j : ZMod N) :
    evenPart f j = (f j + f (-j)) / 2 := rfl

/-- The counting `ℓ^p` norm. -/
@[lyons_tag "def_norm"]
noncomputable def countNorm (f : ZMod N → ℂ) (p : ℝ) : ℝ :=
  (∑ j : ZMod N, ‖f j‖ ^ p) ^ (1 / p)

/-! ### Negating the frequency -/

/-- For an **even** function the transform is even. -/
theorem dft_neg_of_even {f : ZMod N → ℂ} (hf : ∀ j, f (-j) = f j) (k : ZMod N) :
    𝓕 f (-k) = 𝓕 f k := by
  rw [dft_apply, dft_apply]
  refine (Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j => ?_).symm
  simp only [Equiv.neg_apply]
  rw [hf j]
  congr 2
  ring

/-- For a **real-valued** function, negating the frequency conjugates the
transform. -/
theorem dft_neg_of_real {f : ZMod N → ℂ} (hf : ∀ j, conj (f j) = f j) (k : ZMod N) :
    𝓕 f (-k) = conj (𝓕 f k) := by
  rw [dft_apply, dft_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, hf j, ZMod.conj_stdAddChar]
  congr 2
  ring

/-! ### The even part through the transform -/

/-- **The transform determines the function.** Immediate from Mathlib's
`ZMod.dft_dft`: applying the transform twice recovers `N • f ∘ (-·)`. -/
theorem dft_injective : Function.Injective (dft : (ZMod N → ℂ) → ZMod N → ℂ) := by
  intro f h hfh
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  funext j
  have hj := congrFun (congrArg dft hfh) (-j)
  simp only [dft_dft, neg_neg, smul_eq_mul] at hj
  exact mul_left_cancel₀ hN hj

/-- **The transform of the even part is the real part of the transform.** -/
@[lyons_tag "lem_dft_even_part"]
theorem dft_evenPart {f : ZMod N → ℂ} (hf : ∀ j, conj (f j) = f j) (k : ZMod N) :
    𝓕 (evenPart f) k = (((𝓕 f k).re : ℝ) : ℂ) := by
  -- Reindexing by negation turns `𝓕 f (-k)` into the transform of `f ∘ (-·)`.
  have hneg : 𝓕 f (-k) = ∑ j : ZMod N, (stdAddChar (-(j * k)) : ℂ) * f (-j) := by
    rw [dft_apply]
    refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j => ?_
    simp only [Equiv.neg_apply, smul_eq_mul, neg_mul, mul_neg, neg_neg]
  have hsplit : 𝓕 (evenPart f) k = (𝓕 f k + 𝓕 f (-k)) / 2 := by
    rw [hneg, dft_apply, dft_apply, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [evenPart_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hsplit, dft_neg_of_real hf, Complex.add_conj]
  push_cast
  ring

/-- **Equal real parts of the transforms means equal even parts.** -/
@[lyons_tag "lem_even_part_eq"]
theorem evenPart_eq_of_re_dft_eq {f h : ZMod N → ℂ}
    (hfr : ∀ j, conj (f j) = f j) (hhr : ∀ j, conj (h j) = h j)
    (hre : ∀ k, (𝓕 f k).re = (𝓕 h k).re) : evenPart f = evenPart h :=
  dft_injective (funext fun k => by rw [dft_evenPart hfr, dft_evenPart hhr, hre])

/-- Pairing an **even** weight against a function sees only its even part. -/
@[lyons_tag "lem_even_pairing"]
theorem sum_mul_evenPart (φ ψ : ZMod N → ℂ) (hφ : ∀ j, φ (-j) = φ j) :
    ∑ j : ZMod N, φ j * ψ j = ∑ j : ZMod N, φ j * evenPart ψ j := by
  have hhalf : ∑ j : ZMod N, φ j * evenPart ψ j
      = (∑ j : ZMod N, φ j * ψ j) / 2 + (∑ j : ZMod N, φ j * ψ (-j)) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [evenPart_apply]
    ring
  -- Reindexing by negation turns the second sum into the first.
  have hneg : ∑ j : ZMod N, φ j * ψ (-j) = ∑ j : ZMod N, φ j * ψ j :=
    Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j => by
      simp only [Equiv.neg_apply]
      rw [hφ j]
  rw [hhalf, hneg]
  ring

end ZMod
