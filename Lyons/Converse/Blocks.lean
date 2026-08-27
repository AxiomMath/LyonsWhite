/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.CyclicChar
import Lyons.Converse.TestElement
import Lyons.InversionExtension.Blocks

/-!
# The Fourier data of the test element

The two facts about `ξ_{n,K,ε}` that the failure of rate-monotonicity is read off
from: its blocks `ρ_{χ_k,1}(ξ)` at every cyclic character, and the non-vanishing
of every one of its coefficients.

## Main results

* `Lyons.Converse.rhoAlg_testElement` : the blocks `ρ_{χ_k,1}(ξ_{n,K,ε})`.
* `Lyons.Converse.coeff_testElement_ne_zero` : every coefficient of
  `ξ_{n,K,ε}` is nonzero.

## Implementation notes

The conventions are those fixed by `Lyons.Converse.TestElement` and
`Lyons.Converse.CyclicChar`: the cyclic group `C` of order `n` with
generator `c` is the additive `ZMod n` with `c = 1`, so `z = 1` and `d = 1`
become `z = 0` and `d = 0`, and the angle `2πj/n` at a residue `j` is read at the
`ZMod.val` lift.

Since `C` is the concrete `ZMod n`, the two hypotheses that
`Lyons.Converse.cyclicAddChar` carries — that `C` has `n` elements and that `c`
generates it — are discharged once and for all by `ZMod.card` and
`Lyons.Converse.exists_zsmul_one`, and `χ_k` is spelled
`cyclicAddChar (ZMod.card n) exists_zsmul_one k` throughout.  No abbreviation is
introduced for it: the character dictionary already names the object, and a
second name for the same function would be a shadow.

The exponential sums are run through `Lyons.Converse.omegaZPow`, which is `ω_n`
at an *integer* exponent.  `Lyons.Converse.omegaN` is raised to an exponent read
in `ℤ/n`, which is right for the orthogonality relation
`Lyons.Converse.sum_omegaN_pow` but not for the algebra here, where the
exponents `k ± 1` and `k ± K` are produced by splitting cosines and sines into
`ω_n^{±qj}` and are naturally integers.
-/

namespace Lyons.Converse

open Finset Real
open scoped ComplexConjugate

variable {n : ℕ} [NeZero n]

/-! ### The standard cyclic model

The cyclic group `C` of order `n` with generator `c` is `ZMod n` with `c = 1`.
`ZMod.card` is the first of the two hypotheses that
`Lyons.Converse.cyclicChar` takes; this is the second. -/

/-- **`1` generates `ZMod n`.**  The `hgen` hypothesis of the cyclic character
dictionary at the standard model `C = ZMod n`, `c = 1`, where `c^j` is the
residue `j` itself. -/
theorem exists_zsmul_one (x : ZMod n) : ∃ j : ℤ, j • (1 : ZMod n) = x :=
  ⟨(x.val : ℤ), by rw [zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_zmod_val]⟩

/-! ### `ω_n` at an integer exponent

Four facts carry every computation below: `omegaZPow` is multiplicative in the
exponent, sees the exponent only through its residue mod `n`, splits a cosine or
a sine of `2πm/n` into two terms, and agrees with `omegaN n ^ ·` on the
`ZMod.val` lift — which is the bridge to the orthogonality sum
`Lyons.Converse.sum_omegaN_pow`.

`Lyons.Converse.omegaN` is already `e^{2πi/n}`, so `omegaZPow n m` is
definitionally `ω_n^m` for `m ≥ 0`; the point of the definition is that the
exponent may be negative, which is unavoidable once `cos(2πqj/n)` is written as
`(ω_n^{qj} + ω_n^{-qj})/2`. -/

section OmegaZPow

omit [NeZero n]

/-- `ω_n` at an integer exponent, `ω_n^m = e^{2πim/n}`, with the exponent taken
in `ℤ` rather than in `ℤ/n`. -/
private noncomputable def omegaZPow (n : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (Complex.ofReal (2 * π * (m : ℝ) / n) * Complex.I)

/-- `ω_n^m` in rectangular form. -/
private theorem omegaZPow_apply (m : ℤ) :
    omegaZPow n m = Complex.ofReal (Real.cos (2 * π * (m : ℝ) / n))
      + Complex.ofReal (Real.sin (2 * π * (m : ℝ) / n)) * Complex.I := by
  rw [omegaZPow, Complex.exp_ofReal_mul_I]

/-- `ω_n^{-m}` is the complex conjugate of `ω_n^m`. -/
private theorem omegaZPow_neg (m : ℤ) :
    omegaZPow n (-m) = Complex.ofReal (Real.cos (2 * π * (m : ℝ) / n))
      - Complex.ofReal (Real.sin (2 * π * (m : ℝ) / n)) * Complex.I := by
  rw [omegaZPow_apply, show (2 * π * ((-m : ℤ) : ℝ) / n) = -(2 * π * (m : ℝ) / n) from by
      push_cast; ring, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- **The cosine split**, `cos(2πm/n) = (ω_n^m + ω_n^{-m})/2`. -/
private theorem ofReal_cos_eq (m : ℤ) :
    Complex.ofReal (Real.cos (2 * π * (m : ℝ) / n))
      = (omegaZPow n m + omegaZPow n (-m)) / 2 := by
  rw [omegaZPow_apply, omegaZPow_neg]; ring

/-- **The sine split**, `sin(2πm/n) = -i(ω_n^m - ω_n^{-m})/2`, with `1/i`
written as `-i` so that no division by `i` occurs. -/
private theorem ofReal_sin_eq (m : ℤ) :
    Complex.ofReal (Real.sin (2 * π * (m : ℝ) / n))
      = -Complex.I * (omegaZPow n m - omegaZPow n (-m)) / 2 := by
  rw [omegaZPow_apply, omegaZPow_neg]
  linear_combination Complex.ofReal (Real.sin (2 * π * (m : ℝ) / n)) * Complex.I_sq

/-- The exponent is additive. -/
private theorem omegaZPow_add (a b : ℤ) :
    omegaZPow n a * omegaZPow n b = omegaZPow n (a + b) := by
  rw [omegaZPow, omegaZPow, omegaZPow, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At the `ZMod.val` lift, `omegaZPow` is the `omegaN` power of
`Lyons.Converse.omegaN`. -/
private theorem omegaZPow_val (r : ZMod n) : omegaZPow n (r.val : ℤ) = omegaN n ^ r.val := by
  rw [omegaZPow, omegaN, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end OmegaZPow

/-- The exponent matters only modulo `n`. -/
private theorem omegaZPow_congr {a b : ℤ} (h : ((a : ZMod n)) = ((b : ZMod n))) :
    omegaZPow n a = omegaZPow n b := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).mp h
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hb : (b : ℂ) = (a : ℂ) + (n : ℂ) * (q : ℂ) := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hq
    push_cast at this
    linear_combination this
  have key : Complex.ofReal (2 * π * (b : ℝ) / n) * Complex.I
      = Complex.ofReal (2 * π * (a : ℝ) / n) * Complex.I
        + (q : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    rw [hb]
    field_simp
  rw [omegaZPow, omegaZPow, key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The orthogonality sum**, `∑_j ω_n^{qj}` is `n` when `q ≡ 0` and `0`
otherwise.  This is `Lyons.Converse.sum_omegaN_pow`, transported to an integer
exponent. -/
private theorem sum_omegaZPow (q : ℤ) :
    ∑ j : ZMod n, omegaZPow n (q * (j.val : ℤ))
      = (n : ℂ) * if ((q : ZMod n)) = 0 then 1 else 0 := by
  have h : ∀ j : ZMod n, omegaZPow n (q * (j.val : ℤ)) = omegaN n ^ (((q : ZMod n)) * j).val :=
    fun j => by
      rw [← omegaZPow_val]
      exact omegaZPow_congr (by push_cast [ZMod.natCast_zmod_val]; ring)
  rw [Finset.sum_congr rfl fun j _ => h j, sum_omegaN_pow]
  split <;> simp

/-- The value of `χ_k` at the residue `j`, as `ω_n^{kj}` with an integer
exponent.  This is the defining prescription `cyclicChar_apply_index` at the
standard model, where `c^j` is `j` itself. -/
private theorem cyclicAddChar_apply_omegaZPow (k j : ZMod n) :
    cyclicAddChar (ZMod.card n) exists_zsmul_one k j
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) := by
  have hj : (j.val : ℕ) • (1 : ZMod n) = j := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have h1 : cyclicChar (ZMod.card n) (exists_zsmul_one (n := n)) k j
      = omegaN n ^ (k * j).val :=
    calc cyclicChar (ZMod.card n) (exists_zsmul_one (n := n)) k j
        = cyclicChar (ZMod.card n) (exists_zsmul_one (n := n)) k ((j.val : ℕ) • (1 : ZMod n)) := by
          rw [hj]
      _ = omegaN n ^ (k * j).val := cyclicChar_apply_index k j
  rw [show cyclicAddChar (ZMod.card n) exists_zsmul_one k j
      = cyclicChar (ZMod.card n) (exists_zsmul_one (n := n)) k j from rfl, h1, ← omegaZPow_val]
  exact omegaZPow_congr (by push_cast [ZMod.natCast_zmod_val]; ring)

/-! ### The two block transforms of the test element -/

/-- A single term of the transform `U^ξ(χ_k)`, with the cosines of
`co_testElement_rot` split into the four frequencies `k ± 1` and `k ± K`. -/
private theorem uCoeff_mul_char (K : ℤ) (ε : ℝ) (k j : ZMod n) :
    InvExtBlock.uCoeff (testElement n K ε) j
        * cyclicAddChar (ZMod.card n) exists_zsmul_one k j
      = (n : ℂ)⁻¹ * (omegaZPow n (((k.val : ℤ) + 1) * (j.val : ℤ))
          + omegaZPow n (((k.val : ℤ) - 1) * (j.val : ℤ))
          + (ε : ℂ) * omegaZPow n (((k.val : ℤ) + K) * (j.val : ℤ))
          + (ε : ℂ) * omegaZPow n (((k.val : ℤ) - K) * (j.val : ℤ))) := by
  have hc1 : Complex.ofReal (Real.cos (2 * π * (j.val : ℝ) / n))
      = (omegaZPow n (j.val : ℤ) + omegaZPow n (-(j.val : ℤ))) / 2 := by
    rw [show (2 * π * (j.val : ℝ) / n) = 2 * π * (((j.val : ℤ) : ℝ)) / n from by push_cast; ring]
    exact ofReal_cos_eq _
  have hc2 : Complex.ofReal (Real.cos (2 * π * (K * (j.val : ℤ) : ℝ) / n))
      = (omegaZPow n (K * (j.val : ℤ)) + omegaZPow n (-(K * (j.val : ℤ)))) / 2 := by
    rw [show (2 * π * (K * (j.val : ℤ) : ℝ) / n)
        = 2 * π * (((K * (j.val : ℤ) : ℤ) : ℝ)) / n from by push_cast; ring]
    exact ofReal_cos_eq _
  have e1 : omegaZPow n (((k.val : ℤ) + 1) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (j.val : ℤ) := by
    rw [omegaZPow_add,
      show (k.val : ℤ) * (j.val : ℤ) + (j.val : ℤ) = ((k.val : ℤ) + 1) * (j.val : ℤ) from by ring]
  have e2 : omegaZPow n (((k.val : ℤ) - 1) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (-(j.val : ℤ)) := by
    rw [omegaZPow_add,
      show (k.val : ℤ) * (j.val : ℤ) + -(j.val : ℤ) = ((k.val : ℤ) - 1) * (j.val : ℤ) from by ring]
  have e3 : omegaZPow n (((k.val : ℤ) + K) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (K * (j.val : ℤ)) := by
    rw [omegaZPow_add, show (k.val : ℤ) * (j.val : ℤ) + K * (j.val : ℤ)
      = ((k.val : ℤ) + K) * (j.val : ℤ) from by ring]
  have e4 : omegaZPow n (((k.val : ℤ) - K) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (-(K * (j.val : ℤ))) := by
    rw [omegaZPow_add, show (k.val : ℤ) * (j.val : ℤ) + -(K * (j.val : ℤ))
      = ((k.val : ℤ) - K) * (j.val : ℤ) from by ring]
  simp only [InvExtBlock.uCoeff]
  rw [co_testElement_rot, cyclicAddChar_apply_omegaZPow, e1, e2, e3, e4]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast]
  rw [hc1, hc2]
  ring

/-- A single term of the transform `V^{ξ,1}(χ_k)`.  Same split as
`uCoeff_mul_char`, except that the sine of `co_testElement_refl` makes the two
`±K` frequencies enter with opposite signs and a factor `i`. -/
private theorem vCoeff_mul_char (K : ℤ) (ε : ℝ) (k j : ZMod n) :
    InvExtBlock.vCoeff (testElement n K ε) 0 j
        * cyclicAddChar (ZMod.card n) exists_zsmul_one k j
      = (n : ℂ)⁻¹ * (omegaZPow n (((k.val : ℤ) + 1) * (j.val : ℤ))
          + omegaZPow n (((k.val : ℤ) - 1) * (j.val : ℤ))
          - (ε : ℂ) * Complex.I * omegaZPow n (((k.val : ℤ) + K) * (j.val : ℤ))
          + (ε : ℂ) * Complex.I * omegaZPow n (((k.val : ℤ) - K) * (j.val : ℤ))) := by
  have hc1 : Complex.ofReal (Real.cos (2 * π * (j.val : ℝ) / n))
      = (omegaZPow n (j.val : ℤ) + omegaZPow n (-(j.val : ℤ))) / 2 := by
    rw [show (2 * π * (j.val : ℝ) / n) = 2 * π * (((j.val : ℤ) : ℝ)) / n from by push_cast; ring]
    exact ofReal_cos_eq _
  have hs2 : Complex.ofReal (Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n))
      = -Complex.I * (omegaZPow n (K * (j.val : ℤ)) - omegaZPow n (-(K * (j.val : ℤ)))) / 2 := by
    rw [show (2 * π * (K * (j.val : ℤ) : ℝ) / n)
        = 2 * π * (((K * (j.val : ℤ) : ℤ) : ℝ)) / n from by push_cast; ring]
    exact ofReal_sin_eq _
  have e1 : omegaZPow n (((k.val : ℤ) + 1) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (j.val : ℤ) := by
    rw [omegaZPow_add,
      show (k.val : ℤ) * (j.val : ℤ) + (j.val : ℤ) = ((k.val : ℤ) + 1) * (j.val : ℤ) from by ring]
  have e2 : omegaZPow n (((k.val : ℤ) - 1) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (-(j.val : ℤ)) := by
    rw [omegaZPow_add,
      show (k.val : ℤ) * (j.val : ℤ) + -(j.val : ℤ) = ((k.val : ℤ) - 1) * (j.val : ℤ) from by ring]
  have e3 : omegaZPow n (((k.val : ℤ) + K) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (K * (j.val : ℤ)) := by
    rw [omegaZPow_add, show (k.val : ℤ) * (j.val : ℤ) + K * (j.val : ℤ)
      = ((k.val : ℤ) + K) * (j.val : ℤ) from by ring]
  have e4 : omegaZPow n (((k.val : ℤ) - K) * (j.val : ℤ))
      = omegaZPow n ((k.val : ℤ) * (j.val : ℤ)) * omegaZPow n (-(K * (j.val : ℤ))) := by
    rw [omegaZPow_add, show (k.val : ℤ) * (j.val : ℤ) + -(K * (j.val : ℤ))
      = ((k.val : ℤ) - K) * (j.val : ℤ) from by ring]
  simp only [InvExtBlock.vCoeff, add_zero]
  rw [co_testElement_refl, cyclicAddChar_apply_omegaZPow, e1, e2, e3, e4]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast]
  rw [hc1, hs2]
  ring

/-- **The abelian transform of the test element.**  The four frequencies
contribute an indicator each, with no distinctness assumed — that is what turns
them into the four cases of `rhoAlg_testElement`. -/
private theorem Ublock_testElement (K : ℤ) (ε : ℝ) (k : ZMod n) :
    InvExtBlock.Ublock (testElement n K ε) (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
      = (if k = -1 then 1 else 0) + (if k = 1 then 1 else 0)
        + (ε : ℂ) * (if k = -(K : ZMod n) then 1 else 0)
        + (ε : ℂ) * (if k = (K : ZMod n) then 1 else 0) := by
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have q1 : ((((k.val : ℤ) + 1 : ℤ)) : ZMod n) = k + 1 := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have q2 : ((((k.val : ℤ) - 1 : ℤ)) : ZMod n) = k - 1 := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have q3 : ((((k.val : ℤ) + K : ℤ)) : ZMod n) = k + (K : ZMod n) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have q4 : ((((k.val : ℤ) - K : ℤ)) : ZMod n) = k - (K : ZMod n) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [InvExtBlock.Ublock, AddCharFourier.dft_apply,
    Finset.sum_congr rfl fun j _ => uCoeff_mul_char K ε k j, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_omegaZPow, sum_omegaZPow, sum_omegaZPow,
    sum_omegaZPow]
  simp only [q1, q2, q3, q4, add_eq_zero_iff_eq_neg, sub_eq_zero]
  field_simp

/-- **The outside transform of the test element**, the companion of
`Ublock_testElement`. -/
private theorem Vblock_testElement (K : ℤ) (ε : ℝ) (k : ZMod n) :
    InvExtBlock.Vblock (testElement n K ε) 0 (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
      = (if k = -1 then 1 else 0) + (if k = 1 then 1 else 0)
        - (ε : ℂ) * Complex.I * (if k = -(K : ZMod n) then 1 else 0)
        + (ε : ℂ) * Complex.I * (if k = (K : ZMod n) then 1 else 0) := by
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have q1 : ((((k.val : ℤ) + 1 : ℤ)) : ZMod n) = k + 1 := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have q2 : ((((k.val : ℤ) - 1 : ℤ)) : ZMod n) = k - 1 := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have q3 : ((((k.val : ℤ) + K : ℤ)) : ZMod n) = k + (K : ZMod n) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  have q4 : ((((k.val : ℤ) - K : ℤ)) : ZMod n) = k - (K : ZMod n) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [InvExtBlock.Vblock, AddCharFourier.dft_apply,
    Finset.sum_congr rfl fun j _ => vCoeff_mul_char K ε k j, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_omegaZPow, sum_omegaZPow, sum_omegaZPow,
    sum_omegaZPow]
  simp only [q1, q2, q3, q4, add_eq_zero_iff_eq_neg, sub_eq_zero]
  field_simp

/-! ### The blocks of the test element -/

/-- `ρ_{χ_k,1}` at the test element, assembled from the two transforms.  It is
isolated so that the case analysis below happens once rather than once per matrix
entry: the `χ(z)` factor of `InvExtBlock.rhoAlg_entries` is `1` because
`z = 0`. -/
private theorem rhoAlg_testElement_of (K : ℤ) (ε : ℝ) (k : ZMod n) {u v : ℂ}
    (hu : InvExtBlock.Ublock (testElement n K ε)
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) = u)
    (hv : InvExtBlock.Vblock (testElement n K ε) 0
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) = v) :
    InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n)
        (testElement n K ε) = !![u, v; conj v, conj u] := by
  rw [InvExtBlock.rhoAlg_entries, hu, hv, AddChar.map_zero_eq_one, one_mul]

/-- **The blocks of the test element.**  `ρ_{χ_k,1}(ξ_{n,K,ε})` is
`!![1,1;1,1]` at `k = ±1`, `ε • !![1,i;-i,1]` at `k = K`, `ε • !![1,-i;i,1]` at
`k = -K`, and `0` at every other `k`.

Here `ρ_{χ_k,1}` is `rhoAlg (χ_k) 0`, since `d = 1` is the neutral element of the
additively written `C = ZMod n`, and `χ_k` is
`cyclicAddChar (ZMod.card n) exists_zsmul_one k`.

**Where the hypotheses are used.**  `hK` and `hn` enter only through the pairwise
distinctness of the four residues `1`, `-1`, `K`, `-K` of `ℤ/n`: without that,
two of the four indicators of `Ublock_testElement` could fire at the same `k` and
the value would be a sum.  Concretely the four facts needed are that `2`,
`K - 1`, `K + 1` and `2K` are all nonzero in `ℤ/n`, and each is an integer
strictly between `0` and `n`.  `K ≥ 2` is all that distinctness needs — `K = 1`
is exactly the excluded case, where `K` and `1` are the same residue.

No sign hypothesis on `ε` is needed; see the notes of
`Lyons.Converse.TestElement`. -/
@[lyons_tag "lem_x_eps_block"]
theorem rhoAlg_testElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε : ℝ) (k : ZMod n) :
    InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n)
        (testElement n K ε)
      = if k = 1 ∨ k = -1 then !![1, 1; 1, 1]
        else if k = (K : ZMod n) then ε • !![1, Complex.I; -Complex.I, 1]
        else if k = -(K : ZMod n) then ε • !![1, -Complex.I; Complex.I, 1]
        else 0 := by
  -- The four residues `1`, `-1`, `K`, `-K` are pairwise distinct.
  have hcast : ∀ m : ℤ, 0 < m → m < (n : ℤ) → ((m : ZMod n)) ≠ 0 := by
    intro m h0 hm
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hdvd => absurd (Int.le_of_dvd h0 hdvd) (by omega)
  have c2 : (2 : ZMod n) ≠ 0 := by
    have h := hcast 2 (by norm_num) (by omega)
    push_cast at h
    exact h
  have cKm : (K : ZMod n) - 1 ≠ 0 := by
    have h := hcast (K - 1) (by omega) (by omega)
    push_cast at h
    exact h
  have cKp : (K : ZMod n) + 1 ≠ 0 := by
    have h := hcast (K + 1) (by omega) (by omega)
    push_cast at h
    exact h
  have c2K : 2 * (K : ZMod n) ≠ 0 := by
    have h := hcast (2 * K) (by omega) (by omega)
    push_cast at h
    exact h
  -- The four cases, each fixing the values of the two transforms.
  rcases eq_or_ne k 1 with rfl | hk1
  · have hu : InvExtBlock.Ublock (testElement n K ε)
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (1 : ZMod n)) = 1 := by
      rw [Ublock_testElement, if_neg fun h => c2 (by linear_combination h), if_pos rfl,
        if_neg fun h => cKp (by linear_combination h),
        if_neg fun h => cKm (by linear_combination -h)]
      ring
    have hv : InvExtBlock.Vblock (testElement n K ε) 0
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (1 : ZMod n)) = 1 := by
      rw [Vblock_testElement, if_neg fun h => c2 (by linear_combination h), if_pos rfl,
        if_neg fun h => cKp (by linear_combination h),
        if_neg fun h => cKm (by linear_combination -h)]
      ring
    rw [rhoAlg_testElement_of K ε 1 hu hv, if_pos (Or.inl rfl)]
    simp
  rcases eq_or_ne k (-1) with rfl | hkm1
  · have hu : InvExtBlock.Ublock (testElement n K ε)
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (-1 : ZMod n)) = 1 := by
      rw [Ublock_testElement, if_pos rfl, if_neg fun h => c2 (by linear_combination -h),
        if_neg fun h => cKm (by linear_combination h),
        if_neg fun h => cKp (by linear_combination -h)]
      ring
    have hv : InvExtBlock.Vblock (testElement n K ε) 0
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (-1 : ZMod n)) = 1 := by
      rw [Vblock_testElement, if_pos rfl, if_neg fun h => c2 (by linear_combination -h),
        if_neg fun h => cKm (by linear_combination h),
        if_neg fun h => cKp (by linear_combination -h)]
      ring
    rw [rhoAlg_testElement_of K ε (-1) hu hv, if_pos (Or.inr rfl)]
    simp
  rw [if_neg (by rintro (h | h) <;> [exact hk1 h; exact hkm1 h])]
  rcases eq_or_ne k (K : ZMod n) with rfl | hkK
  · have hu : InvExtBlock.Ublock (testElement n K ε)
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (K : ZMod n)) = (ε : ℂ) := by
      rw [Ublock_testElement, if_neg fun h => cKp (by linear_combination h),
        if_neg fun h => cKm (by linear_combination h),
        if_neg fun h => c2K (by linear_combination h), if_pos rfl]
      ring
    have hv : InvExtBlock.Vblock (testElement n K ε) 0
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (K : ZMod n)) = (ε : ℂ) * Complex.I := by
      rw [Vblock_testElement, if_neg fun h => cKp (by linear_combination h),
        if_neg fun h => cKm (by linear_combination h),
        if_neg fun h => c2K (by linear_combination h), if_pos rfl]
      ring
    rw [rhoAlg_testElement_of K ε (K : ZMod n) hu hv, if_pos rfl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [if_neg hkK]
  rcases eq_or_ne k (-(K : ZMod n)) with rfl | hkmK
  · have hu : InvExtBlock.Ublock (testElement n K ε)
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (-(K : ZMod n))) = (ε : ℂ) := by
      rw [Ublock_testElement, if_neg fun h => cKm (by linear_combination -h),
        if_neg fun h => cKp (by linear_combination -h), if_pos rfl,
        if_neg fun h => c2K (by linear_combination -h)]
      ring
    have hv : InvExtBlock.Vblock (testElement n K ε) 0
        (cyclicAddChar (ZMod.card n) exists_zsmul_one (-(K : ZMod n)))
          = -((ε : ℂ) * Complex.I) := by
      rw [Vblock_testElement, if_neg fun h => cKm (by linear_combination -h),
        if_neg fun h => cKp (by linear_combination -h), if_pos rfl,
        if_neg fun h => c2K (by linear_combination -h)]
      ring
    rw [rhoAlg_testElement_of K ε (-(K : ZMod n)) hu hv, if_pos rfl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [if_neg hkmK]
  have hu : InvExtBlock.Ublock (testElement n K ε)
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) = 0 := by
    rw [Ublock_testElement, if_neg hkm1, if_neg hk1, if_neg hkmK, if_neg hkK]
    ring
  have hv : InvExtBlock.Vblock (testElement n K ε) 0
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) = 0 := by
    rw [Vblock_testElement, if_neg hkm1, if_neg hk1, if_neg hkmK, if_neg hkK]
    ring
  rw [rhoAlg_testElement_of K ε k hu hv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ### Non-vanishing of the coefficients -/

/-- **No coefficient of the test element vanishes.**

The natural hypothesis is `0 < ε < min_{j ∈ ℤ/n} |cos(2πj/n)|`; over a finite
index type that minimum bound is the pointwise bound `hε` below, which is the
form the proof consumes and the form a caller can supply without naming a
`Finset.inf'`.

The claim `(ξ_{n,K,ε})_g ≠ 0` for `g ∈ G` is `co (testElement n K ε) g ≠ 0` for
`g : InvExt (ZMod n) 0`; the case split on `g` is the concrete model's form of
the normal form of an inversion extension.

Both cases are the same estimate.  Writing `y = cos(2πj/n)`, the coefficient is
`(2/n)(y + ε t)` with `t` a cosine or a sine, so `|ε t| ≤ ε < |y|` and the sum
cannot vanish; `2/n ≠ 0` because `n ≠ 0`.

The hypothesis is satisfiable exactly when the minimum is positive, which for
odd `n` is `Lyons.Converse.cos_two_pi_div_ne_zero`; oddness of `n` is *not*
needed for this lemma, only for producing an `ε` that meets its hypothesis. -/
@[lyons_tag "lem_x_eps_coeff_ne_zero"]
theorem coeff_testElement_ne_zero (K : ℤ) {ε : ℝ} (hε₀ : 0 < ε)
    (hε : ∀ j : ZMod n, ε < |Real.cos (2 * π * (j.val : ℝ) / n)|)
    (g : InvExt (ZMod n) 0) : co (testElement n K ε) g ≠ 0 := by
  have hn : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- The shared estimate: a perturbation of size at most `ε` cannot cancel `y`.
  have key : ∀ (j : ZMod n) (t : ℝ), |t| ≤ 1 →
      2 / n * (Real.cos (2 * π * (j.val : ℝ) / n) + ε * t) ≠ 0 := by
    intro j t ht hzero
    set y := Real.cos (2 * π * (j.val : ℝ) / n) with hy
    have hsum : y + ε * t = 0 := by
      field_simp at hzero
      linarith [hzero]
    have habs : |ε * t| < |y| := by
      calc |ε * t| = ε * |t| := by rw [abs_mul, abs_of_pos hε₀]
        _ ≤ ε := by nlinarith [abs_nonneg t]
        _ < |y| := hε j
    rw [show ε * t = -y by linarith, abs_neg] at habs
    exact absurd habs (lt_irrefl _)
  cases g with
  | rot j =>
    rw [co_testElement_rot]
    exact key j _ (Real.abs_cos_le_one _)
  | refl j =>
    rw [co_testElement_refl]
    exact key j _ (Real.abs_sin_le_one _)

end Lyons.Converse
