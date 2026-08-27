/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Lyons.Meta.Tag

/-!
# The Fourier layer over an arbitrary finite abelian group

`Lyons.Fourier.Parseval` and `Lyons.Fourier.Majorant` develop the unnormalized
discrete Fourier transform on `ZMod N`. `Lyons.rateMonotonic_invExt_even` needs
the same four facts over an arbitrary finite abelian group `A`, with the dual
group `AddChar A ℂ` in place of `ZMod N` as the frequency domain. This file
supplies them.

## Main results

* `sum_char_apply` : character orthogonality summed over the dual,
  `∑ χ, χ a = if a = 0 then |A| else 0`.
* `sum_dft_mul_conj` : the polarised Parseval identity,
  `∑ χ, f̂ χ * conj (ĝ χ) = |A| * ∑ a, f a * conj (g a)`.
* `sum_norm_sq_dft` : Parseval, `∑ a, ‖f a‖ ^ 2 = |A|⁻¹ * ∑ χ, ‖f̂ χ‖ ^ 2`.
* `dft_mul` : the transform of a pointwise product, as a convolution over the
  dual.
* `sum_pow_le_of_dft_le` : the even-exponent majorant inequality.

## Relation to the cyclic development

The cyclic proofs port essentially verbatim, because the load-bearing input is
available in general: `AddChar.sum_apply_eq_ite` is the general-`A`
orthogonality relation, standing in for `ZMod.sum_stdAddChar_mul`, and both
Parseval and the product formula are *derived from* orthogonality by exchanging
the order of summation.

The one step that does not transcribe is conjugation. The cyclic proof gets
`conj (stdAddChar x) = stdAddChar (-x)` from the explicit root-of-unity form of
`ZMod.stdAddChar`, which a general `AddChar A ℂ` does not have. What replaces it
is finiteness: every element of a finite group has finite order, so every
character value is a root of unity, `AddChar.norm_apply` gives `‖χ a‖ = 1`, and
`AddChar.map_neg_eq_conj` gives `χ (-a) = conj (χ a)`. That is exactly the form
the derivations consume, via `char_mul_conj` below.

`dft_mul` has no Mathlib counterpart in either setting. Here the frequency
domain is the dual, which is itself an `AddCommGroup` (`AddChar.instAddCommGroup`),
so `χ - ψ` is meaningful and the right-hand side is a genuine convolution.

## Implementation notes

The transform is unnormalized, `f̂(χ) = ∑ a, f a * χ a`, matching both the source
paper and Mathlib's `ZMod.dft`. The cost is a factor `|A|` in the product
formula and in Parseval, exactly as in the cyclic files, which keeps the
downstream constants unchanged.

The general-`A` convolution `dconv` and the induction `dft_pow_dominated` are
`private`: they are internal to `sum_pow_le_of_dft_le`, whose statement inlines
the convolution.
-/

namespace Lyons.AddCharFourier

open Finset
open scoped ComplexConjugate

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The **unnormalized Fourier transform** on a finite abelian group:
`f̂(χ) = ∑ a, f a * χ a`. Matches the source's convention and Mathlib's
`ZMod.dft`. The frequency domain is the character group of `A`, which is
Mathlib's `AddChar A ℂ`. -/
@[lyons_tag "def_dft"]
noncomputable def dft (f : A → ℂ) (χ : AddChar A ℂ) : ℂ :=
  ∑ a : A, f a * χ a

theorem dft_apply (f : A → ℂ) (χ : AddChar A ℂ) : dft f χ = ∑ a : A, f a * χ a :=
  rfl

/-- A finite abelian group is nonempty, so `|A|` is invertible in `ℂ`. -/
private theorem card_ne_zero : (Fintype.card A : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨0⟩).ne'

/-- **Character orthogonality**, summing over the dual rather than the group.
A thin wrapper on `AddChar.sum_apply_eq_ite`; the general-`A` analogue of
`ZMod.sum_stdAddChar_mul`. -/
@[lyons_tag "lem_char_orthogonality"]
theorem sum_char_apply (a : A) :
    ∑ χ : AddChar A ℂ, χ a = if a = 0 then (Fintype.card A : ℂ) else 0 :=
  AddChar.sum_apply_eq_ite a

/-- Orthogonality in the form the double-sum manipulations below consume: the
character is evaluated at a difference, and the sum over the dual detects the
diagonal. -/
private theorem sum_char_sub (a b : A) :
    ∑ χ : AddChar A ℂ, χ (a - b) = if a - b = 0 then (Fintype.card A : ℂ) else 0 :=
  sum_char_apply (a - b)

/-- On a finite group, `χ a * conj (χ b) = χ (a - b)`. This replaces
`ZMod.conj_stdAddChar`, which read the same fact off the explicit root-of-unity
form of `ZMod.stdAddChar`; here it comes from `AddChar.map_neg_eq_conj`, which
holds because the values of a character on a finite group are roots of unity. -/
private theorem char_mul_conj (χ : AddChar A ℂ) (a b : A) :
    (χ a) * conj (χ b) = χ (a - b) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]

/-- **The polarised Parseval identity.** The general-`A` form of
`ZMod.sum_dft_mul_conj`: expand a single term into a double sum whose character
depends only on the difference of the two group variables, exchange the order of
summation, and apply orthogonality. -/
@[lyons_tag "lem_dft_polarised"]
theorem sum_dft_mul_conj (f g : A → ℂ) :
    ∑ χ : AddChar A ℂ, dft f χ * (starRingEnd ℂ) (dft g χ)
      = (Fintype.card A : ℂ) * ∑ a : A, f a * (starRingEnd ℂ) (g a) := by
  classical
  -- Expand a single term into a double sum whose character depends only on `a - b`.
  have expand : ∀ χ : AddChar A ℂ, dft f χ * conj (dft g χ)
      = ∑ a : A, ∑ b : A, (χ (a - b)) * (f a * conj (g b)) := by
    intro χ
    rw [dft_apply, dft_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    rw [map_mul]
    calc f a * χ a * (conj (g b) * conj (χ b))
        = (χ a * conj (χ b)) * (f a * conj (g b)) := by ring
      _ = _ := by rw [char_mul_conj]
  rw [Finset.sum_congr rfl fun χ _ ↦ expand χ]
  -- Move the sum over the dual innermost.
  rw [Finset.sum_comm]
  have step : ∀ a : A,
      ∑ χ : AddChar A ℂ, ∑ b : A, (χ (a - b)) * (f a * conj (g b))
        = ∑ b : A, (if a - b = 0 then (Fintype.card A : ℂ) else 0)
            * (f a * conj (g b)) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_mul, sum_char_sub]
  rw [Finset.sum_congr rfl fun a _ ↦ step a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single a]
  · rw [sub_self, if_pos rfl]
  · intro b _ hb
    rw [if_neg (by simpa [sub_eq_zero] using (Ne.symm hb)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Parseval's identity.** The general-`A` form of `ZMod.sum_norm_sq_dft`,
obtained from `sum_dft_mul_conj` at `g = f`. -/
@[lyons_tag "lem_parseval"]
theorem sum_norm_sq_dft (f : A → ℂ) :
    ∑ a : A, ‖f a‖ ^ 2
      = (Fintype.card A : ℝ)⁻¹ * ∑ χ : AddChar A ℂ, ‖dft f χ‖ ^ 2 := by
  have key := sum_dft_mul_conj f f
  have hsq : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj']; norm_cast
  simp only [hsq] at key
  have hcast : ((∑ χ : AddChar A ℂ, ‖dft f χ‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card A : ℝ) * ∑ a : A, ‖f a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast at key ⊢; exact key
  have hreal : (∑ χ : AddChar A ℂ, ‖dft f χ‖ ^ 2 : ℝ)
      = (Fintype.card A : ℝ) * ∑ a : A, ‖f a‖ ^ 2 := by exact_mod_cast hcast
  have hR : (Fintype.card A : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨(0 : A)⟩).ne'
  rw [hreal, inv_mul_cancel_left₀ hR]

/-- **The transform of a pointwise product**, as a convolution over the dual.
Mathlib has no counterpart, and the source's Lemma 2.2 needs the `m`-fold
version of exactly this. The dual `AddChar A ℂ` is itself an `AddCommGroup`, so
`χ - ψ` is meaningful. The general-`A` form of `ZMod.dft_mul`, with the
convolution written out; the multiplicative `χψ⁻¹` is `χ - ψ` in the additive
dual. -/
@[lyons_tag "lem_dft_mul"]
theorem dft_mul (f g : A → ℂ) (χ : AddChar A ℂ) :
    dft (fun a => f a * g a) χ
      = (Fintype.card A : ℂ)⁻¹ * ∑ ψ : AddChar A ℂ, dft f ψ * dft g (χ - ψ) := by
  classical
  -- Expand each convolution term, isolating the `ψ`-character at `a - b`.
  have expand : ∀ ψ : AddChar A ℂ, dft f ψ * dft g (χ - ψ)
      = ∑ a : A, ∑ b : A, (ψ (a - b)) * (χ b * (f a * g b)) := by
    intro ψ
    rw [dft_apply, dft_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    have hpsi : (ψ a) * ψ (-b) = ψ (a - b) := by
      rw [← AddChar.map_add_eq_mul, sub_eq_add_neg]
    calc f a * ψ a * (g b * ((χ - ψ) b))
        = f a * ψ a * (g b * (χ b * ψ (-b))) := by rw [AddChar.sub_apply]
      _ = ((ψ a) * ψ (-b)) * (χ b * (f a * g b)) := by ring
      _ = _ := by rw [hpsi]
  have step : ∀ a : A,
      ∑ ψ : AddChar A ℂ, ∑ b : A, (ψ (a - b)) * (χ b * (f a * g b))
        = ∑ b : A, (if a - b = 0 then (Fintype.card A : ℂ) else 0)
            * (χ b * (f a * g b)) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_mul, sum_char_sub]
  -- Only the diagonal `b = a` survives, leaving `|A|` times the transform.
  have key : ∑ ψ : AddChar A ℂ, dft f ψ * dft g (χ - ψ)
      = (Fintype.card A : ℂ) * dft (fun a => f a * g a) χ := by
    rw [Finset.sum_congr rfl fun ψ _ ↦ expand ψ, Finset.sum_comm,
      Finset.sum_congr rfl fun a _ ↦ step a, dft_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_eq_single a]
    · rw [sub_self, if_pos rfl]; ring
    · intro b _ hb
      rw [if_neg (by simpa [sub_eq_zero] using (Ne.symm hb)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [key, inv_mul_cancel_left₀ card_ne_zero]

/-! ### The `m`-fold majorant step

The port of `Lyons.Fourier.Majorant`. `z = (‖z‖ : ℂ)` says exactly that `z`
is a nonnegative real; closure under products and sums is what the induction
needs. -/

private theorem nonnegReal_mul {z w : ℂ} (hz : z = (‖z‖ : ℂ)) (hw : w = (‖w‖ : ℂ)) :
    z * w = (‖z * w‖ : ℂ) := by
  rw [norm_mul]
  push_cast
  rw [← hz, ← hw]

private theorem nonnegReal_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ)
    (hF : ∀ i ∈ s, F i = (‖F i‖ : ℂ)) :
    ∑ i ∈ s, F i = (‖∑ i ∈ s, F i‖ : ℂ) := by
  have hcast : ∑ i ∈ s, F i = ((∑ i ∈ s, ‖F i‖ : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl hF
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]

/-- Convolution in the Fourier variable, over the dual group. The general-`A`
analogue of `ZMod.dconv`. -/
private noncomputable def dconv (F H : AddChar A ℂ → ℂ) : AddChar A ℂ → ℂ :=
  fun χ => ∑ ψ : AddChar A ℂ, F ψ * H (χ - ψ)

/-- `dft_mul` in the cleared-denominator form the induction uses. -/
private theorem card_mul_dft_mul (f g : A → ℂ) (χ : AddChar A ℂ) :
    (Fintype.card A : ℂ) * dft (f * g) χ = dconv (dft f) (dft g) χ := by
  have hfg : dft (f * g) χ = dft (fun a => f a * g a) χ := rfl
  rw [hfg, dft_mul, dconv, ← mul_assoc, mul_inv_cancel₀ card_ne_zero, one_mul]

/-- The inductive heart of the majorant argument: domination of the transforms
is inherited by pointwise powers, and the majorant's transform stays a
nonnegative real. The two conclusions are proved together because the induction
step needs nonneg-realness at `m` to identify a sum of moduli with the modulus
of a sum; neither half is available on its own.

The general-`A` analogue of `ZMod.dft_pow_dominated`. -/
private theorem dft_pow_dominated (f u : A → ℂ)
    (hu : ∀ χ : AddChar A ℂ, dft u χ = (‖dft u χ‖ : ℂ))
    (hfu : ∀ χ : AddChar A ℂ, ‖dft f χ‖ ≤ ‖dft u χ‖) (m : ℕ) (hm : 1 ≤ m) :
    (∀ χ : AddChar A ℂ, ‖dft (f ^ m) χ‖ ≤ ‖dft (u ^ m) χ‖) ∧
      (∀ χ : AddChar A ℂ, dft (u ^ m) χ = (‖dft (u ^ m) χ‖ : ℂ)) := by
  classical
  have hcard : (Fintype.card A : ℂ) ≠ 0 := card_ne_zero
  have hcardR : (0 : ℝ) < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : A)⟩
  induction m, hm using Nat.le_induction with
  | base => simpa using ⟨hfu, hu⟩
  | succ m hm ih =>
    obtain ⟨ihdom, ihpos⟩ := ih
    -- Rewrite `dft (· ^ (m+1))` through the product formula.
    have key : ∀ (h : A → ℂ) (χ : AddChar A ℂ),
        (Fintype.card A : ℂ) * dft (h ^ (m + 1)) χ = dconv (dft (h ^ m)) (dft h) χ := by
      intro h χ
      have hpow : h ^ (m + 1) = h ^ m * h := by ring
      rw [hpow, card_mul_dft_mul]
    -- Nonneg-realness of the majorant's transform at `m + 1`.
    have hposSucc : ∀ χ : AddChar A ℂ,
        dft (u ^ (m + 1)) χ = (‖dft (u ^ (m + 1)) χ‖ : ℂ) := by
      intro χ
      have hterms : ∀ ψ ∈ (univ : Finset (AddChar A ℂ)),
          dft (u ^ m) ψ * dft u (χ - ψ) = (‖dft (u ^ m) ψ * dft u (χ - ψ)‖ : ℂ) :=
        fun ψ _ ↦ nonnegReal_mul (ihpos ψ) (hu (χ - ψ))
      have hconv : dconv (dft (u ^ m)) (dft u) χ
          = (‖dconv (dft (u ^ m)) (dft u) χ‖ : ℂ) := by
        unfold dconv
        exact nonnegReal_sum _ _ hterms
      have hmul := key u χ
      have hsplit : dft (u ^ (m + 1)) χ
          = (Fintype.card A : ℂ)⁻¹ * dconv (dft (u ^ m)) (dft u) χ := by
        rw [← hmul]
        field_simp
      rw [hsplit, hconv, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      push_cast
      ring
    refine ⟨fun χ ↦ ?_, hposSucc⟩
    -- Domination at `m + 1`, via the triangle inequality on the convolution.
    have hfk := key f χ
    have huk := key u χ
    have hbound : ‖dconv (dft (f ^ m)) (dft f) χ‖
        ≤ ‖dconv (dft (u ^ m)) (dft u) χ‖ := by
      have hle : ‖dconv (dft (f ^ m)) (dft f) χ‖
          ≤ ∑ ψ : AddChar A ℂ, ‖dft (u ^ m) ψ‖ * ‖dft u (χ - ψ)‖ := by
        unfold dconv
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ ↦ ?_)
        rw [norm_mul]
        exact mul_le_mul (ihdom ψ) (hfu (χ - ψ)) (norm_nonneg _) (norm_nonneg _)
      have heq : ∑ ψ : AddChar A ℂ, ‖dft (u ^ m) ψ‖ * ‖dft u (χ - ψ)‖
          = ‖dconv (dft (u ^ m)) (dft u) χ‖ := by
        have hterms : ∀ ψ ∈ (univ : Finset (AddChar A ℂ)),
            dft (u ^ m) ψ * dft u (χ - ψ) = (‖dft (u ^ m) ψ * dft u (χ - ψ)‖ : ℂ) :=
          fun ψ _ ↦ nonnegReal_mul (ihpos ψ) (hu (χ - ψ))
        have hconv : dconv (dft (u ^ m)) (dft u) χ
            = (‖dconv (dft (u ^ m)) (dft u) χ‖ : ℂ) := by
          unfold dconv
          exact nonnegReal_sum _ _ hterms
        have hc : ((∑ ψ : AddChar A ℂ, ‖dft (u ^ m) ψ‖ * ‖dft u (χ - ψ)‖ : ℝ) : ℂ)
            = ((‖dconv (dft (u ^ m)) (dft u) χ‖ : ℝ) : ℂ) := by
          rw [← hconv]
          unfold dconv
          push_cast
          refine Finset.sum_congr rfl fun ψ _ ↦ ?_
          rw [← ihpos ψ, ← hu (χ - ψ)]
        exact_mod_cast hc
      exact hle.trans_eq heq
    -- Divide the bound by `|A|`.
    have hfnorm : ‖dft (f ^ (m + 1)) χ‖
        = (Fintype.card A : ℝ)⁻¹ * ‖dconv (dft (f ^ m)) (dft f) χ‖ := by
      have h1 : (Fintype.card A : ℝ) * ‖dft (f ^ (m + 1)) χ‖
          = ‖dconv (dft (f ^ m)) (dft f) χ‖ := by
        rw [← hfk, norm_mul, Complex.norm_natCast]
      rw [← h1]
      field_simp
    have hunorm : ‖dft (u ^ (m + 1)) χ‖
        = (Fintype.card A : ℝ)⁻¹ * ‖dconv (dft (u ^ m)) (dft u) χ‖ := by
      have h1 : (Fintype.card A : ℝ) * ‖dft (u ^ (m + 1)) χ‖
          = ‖dconv (dft (u ^ m)) (dft u) χ‖ := by
        rw [← huk, norm_mul, Complex.norm_natCast]
      rw [← h1]
      field_simp
    rw [hfnorm, hunorm]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- **The even-exponent majorant inequality over a general finite abelian
group.** The shape the source's Lemma 2.2 consumes: if `û` is a nonnegative real
dominating `|f̂|` pointwise on the dual, then the `2m`-th power sums compare.
The general-`A` form of `ZMod.sum_norm_pow_le`.

The power sums below are the `2m`-th powers of the counting norms, so the
inequality `‖f‖_{2m} ≤ ‖u‖_{2m}` follows by monotonicity of
`t ↦ t^{1/(2m)}`. -/
@[lyons_tag "lem_majorant"]
theorem sum_pow_le_of_dft_le (f u : A → ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hu : ∀ χ : AddChar A ℂ, ((dft u χ).re : ℂ) = dft u χ)
    (hu' : ∀ χ : AddChar A ℂ, 0 ≤ (dft u χ).re)
    (hle : ∀ χ : AddChar A ℂ, ‖dft f χ‖ ≤ (dft u χ).re) :
    ∑ a : A, ‖f a‖ ^ (2 * m) ≤ ∑ a : A, ‖u a‖ ^ (2 * m) := by
  -- `dft u χ` real and nonnegative means its norm is its real part.
  have hnorm : ∀ χ : AddChar A ℂ, ‖dft u χ‖ = (dft u χ).re := by
    intro χ
    conv_lhs => rw [← hu χ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu' χ)]
  have hu2 : ∀ χ : AddChar A ℂ, dft u χ = (‖dft u χ‖ : ℂ) := by
    intro χ; rw [hnorm χ]; exact (hu χ).symm
  have hfu : ∀ χ : AddChar A ℂ, ‖dft f χ‖ ≤ ‖dft u χ‖ := by
    intro χ; rw [hnorm χ]; exact hle χ
  obtain ⟨hdom, -⟩ := dft_pow_dominated f u hu2 hfu m hm
  -- `∑ ‖h a‖ ^ (2m) = ∑ ‖(h ^ m) a‖ ^ 2`: this is where evenness is used.
  have hsplit : ∀ h : A → ℂ,
      ∑ a : A, ‖h a‖ ^ (2 * m) = ∑ a : A, ‖(h ^ m) a‖ ^ 2 := by
    intro h
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Pi.pow_apply, norm_pow, ← pow_mul, mul_comm m 2]
  rw [hsplit f, hsplit u, sum_norm_sq_dft (f ^ m), sum_norm_sq_dft (u ^ m)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ ↦ ?_) (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (hdom χ) 2

end Lyons.AddCharFourier
