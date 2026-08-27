/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Jp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.ZMod.Basic

/-!
# Two trigonometric sums

Two facts about the angles `2πj/n` that the converse direction needs, both
independent of everything else in it.

## Main results

* `Lyons.Converse.cos_two_pi_div_ne_zero` : for odd `n` the cosine never
  vanishes at `2πj/n`.
* `Lyons.Converse.sum_signedPow_cos_mul_sin` : the sine sum against
  `J_p ∘ cos` vanishes.

## Implementation notes

For a residue `j ∈ ℤ/n` the value `cos(2πj/n)` is read by lifting `j` to an
integer, and is independent of the lift.  Here the lift is fixed to `ZMod.val`,
and `cos_two_pi_div_congr` / `sin_two_pi_div_congr` are the independence
statement in the form the reindexing consumes: two integers with the same
residue give the same value.

The sine sum is proved by the reindexing `j ↦ -j` of `ℤ/n` rather than by
pairing `j` with `n - j`.  The two are the same involution, but the reindexing
form needs no case distinction at its fixed points and in particular does not
need `n` odd.
-/

namespace Lyons.Converse

open Finset Real

/-- The angle `2πm/n` depends on the integer `m` only through its residue mod
`n`, as far as the cosine can see; so `cos(2πj/n)` for `j ∈ ℤ/n` does not depend
on the chosen integer lift. -/
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

/-- The sine counterpart of `cos_two_pi_div_congr`. -/
private theorem sin_two_pi_div_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ}
    (h : (a : ZMod n) = (b : ZMod n)) :
    Real.sin (2 * π * a / n) = Real.sin (2 * π * b / n) := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).mp h.symm
  have hab : (a : ℝ) = (b : ℝ) + (n : ℝ) * (q : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hq
    push_cast at this
    linarith
  rw [show 2 * π * (a : ℝ) / n = 2 * π * (b : ℝ) / n + (q : ℝ) * (2 * π) by
        rw [hab]; field_simp,
    Real.sin_add_int_mul_two_pi]

/-- **Cosines at odd order do not vanish.**  For odd `n` and any integer `j`,
`cos(2πj/n) ≠ 0`: otherwise `4j = n(2q+1)` with the right-hand side odd and the
left-hand side even. -/
@[lyons_tag "lem_cos_ne_zero"]
theorem cos_two_pi_div_ne_zero {n : ℕ} (hn : Odd n) (j : ℤ) :
    Real.cos (2 * π * j / n) ≠ 0 := by
  obtain ⟨l, hl⟩ := hn
  have hn0 : ((n : ℝ)) ≠ 0 := by
    rw [hl]; push_cast; positivity
  intro hzero
  obtain ⟨q, hq⟩ := Real.cos_eq_zero_iff.mp hzero
  -- `2πj/n = (2q+1)π/2` gives `4j = n(2q+1)` after clearing `π` and `n`.
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have key : (4 * j : ℝ) = (n : ℝ) * (2 * q + 1) := by
    have := hq
    field_simp at this
    nlinarith [this, hpi, Real.pi_ne_zero]
  have keyZ : (4 * j : ℤ) = (n : ℤ) * (2 * q + 1) := by exact_mod_cast key
  -- The left side is even, the right side a product of two odd integers.
  have hn' : Odd (n : ℤ) := ⟨(l : ℤ), by rw [hl]; push_cast; ring⟩
  have hodd : Odd ((n : ℤ) * (2 * q + 1)) := hn'.mul ⟨q, by ring⟩
  rw [← keyZ] at hodd
  obtain ⟨t, ht⟩ := hodd
  omega

/-- **The sine sum vanishes.**  Reindexing by `j ↦ -j` leaves the sum unchanged
while the cosine is even and the sine odd, so the sum equals its own
negative. -/
@[lyons_tag "lem_sine_sum_zero"]
theorem sum_signedPow_cos_mul_sin (p : ℝ) {n : ℕ} [NeZero n] (K : ℤ) :
    ∑ j : ZMod n, signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
        * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n) = 0 := by
  have hn : n ≠ 0 := NeZero.ne n
  set F : ℤ → ℝ := fun m =>
    signedPow p (Real.cos (2 * π * (m : ℝ) / n)) * Real.sin (2 * π * ((K * m : ℤ) : ℝ) / n)
    with hF
  -- The summand, written as `F` applied to the chosen integer lift.
  have hterm : ∀ j : ZMod n,
      signedPow p (Real.cos (2 * π * (j.val : ℝ) / n))
          * Real.sin (2 * π * (K * (j.val : ℤ) : ℝ) / n) = F (j.val : ℤ) := by
    intro j; rw [hF]; push_cast; ring_nf
  have hFapply : ∀ m : ℤ, F m
      = signedPow p (Real.cos (2 * π * (m : ℝ) / n))
        * Real.sin (2 * π * ((K * m : ℤ) : ℝ) / n) := fun _ => rfl
  -- `F` is odd: the cosine is even and the sine is odd.
  have hodd : ∀ m : ℤ, F (-m) = -F m := by
    intro m
    rw [hFapply, hFapply,
      show 2 * π * ((-m : ℤ) : ℝ) / n = -(2 * π * (m : ℝ) / n) by push_cast; ring,
      show 2 * π * ((K * -m : ℤ) : ℝ) / n = -(2 * π * ((K * m : ℤ) : ℝ) / n) by
        push_cast; ring,
      Real.cos_neg, Real.sin_neg]
    ring
  -- `F` only sees the residue of its argument.
  have hcongr : ∀ a b : ℤ, (a : ZMod n) = (b : ZMod n) → F a = F b := by
    intro a b h
    have hK : ((K * a : ℤ) : ZMod n) = ((K * b : ℤ) : ZMod n) := by push_cast; rw [h]
    rw [hFapply, hFapply, cos_two_pi_div_congr hn h, sin_two_pi_div_congr hn hK]
  -- Reindex by negation: `∑ F ((-j).val) = ∑ F (j.val)`.
  have hreindex : ∑ j : ZMod n, F (((-j).val : ℤ)) = ∑ j : ZMod n, F ((j.val : ℤ)) :=
    Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun j => by simp
  have hneg : ∀ j : ZMod n, F (((-j).val : ℤ)) = -F ((j.val : ℤ)) := by
    intro j
    rw [hcongr _ (-(j.val : ℤ)) (by push_cast [ZMod.natCast_zmod_val]; rfl), hodd]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  have key : ∑ j : ZMod n, F ((j.val : ℤ)) = -∑ j : ZMod n, F ((j.val : ℤ)) :=
    calc ∑ j : ZMod n, F ((j.val : ℤ))
        = ∑ j : ZMod n, F (((-j).val : ℤ)) := hreindex.symm
      _ = ∑ j : ZMod n, -F ((j.val : ℤ)) := Finset.sum_congr rfl fun j _ => hneg j
      _ = -∑ j : ZMod n, F ((j.val : ℤ)) := Finset.sum_neg_distrib _
  linarith

end Lyons.Converse
