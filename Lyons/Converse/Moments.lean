/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Jp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The cosine moments and the negative Fourier coefficient

The analytic core of the converse direction: the chain of identities that
produces, for every real `p ≥ 1` that is not an even integer, an odd frequency at
which the Fourier coefficient of `J_p ∘ cos` is *negative*.  That negativity is
what breaks rate-monotonicity away from the even integers.

The chain is

* `cosMoment p K = ∫_0^{π/2} (cos t)^{p-1} cos (K t) dt`, positive at `K = 1`;
* integration by parts against `cos ((L+1) ·)`, plus the product-to-sum formula,
  gives the recurrence `I_{L+2}(p) = (p-L-1)/(p+L+1) * I_L(p)`;
* iterating it turns the odd moments into products,
  `I_{2M+1}(p) = I_1(p) ∏_{l=1}^{M} (p-2l)/(p+2l)`;
* for `2m < p < 2m+2` exactly one factor of that product is negative, so
  `I_{2m+3}(p) < 0`;
* folding `[0, 2π]` onto `[0, π/2]` identifies `Γ_K(p)` with `(2/π) I_K(p)` for
  odd `K`, hence `Γ_{2m+3}(p) < 0`.

Every power of the cosine is a `Real.rpow`, since `p` is real.  The exponent
`p - 1` is nonnegative, so `t ↦ (cos t)^{p-1}` is continuous even where the
cosine vanishes and no integrability hypothesis has to be carried; the genuinely
discontinuous object is `J_p ∘ cos` at `p = 1`, which is integrated through the
bounded-measurable route in `intervalIntegrable_signedPow_cos`.

## Main definitions

* `Lyons.Converse.cosMoment` : the moment `I_K(p)`.
* `Lyons.Converse.signedPowFourier` : the coefficient `Γ_K(p)`.

## Main results

* `Lyons.Converse.cosMoment_one_pos` : `I_1(p) > 0`.
* `Lyons.Converse.hasDerivAt_cos_rpow` : the derivative of `t ↦ (cos t)^p`.
* `Lyons.Converse.cos_add_two_mul_sub_cos_mul` :
  `cos((l+2)t) - cos(lt) = -2 sin((l+1)t) sin t`.
* `Lyons.Converse.cosMoment_sub_eq` : integration by parts for the moments.
* `Lyons.Converse.two_mul_integral_cos_rpow_mul_cos` : the product-to-sum
  formula, which turns the remaining integral into a sum of two moments.
* `Lyons.Converse.cosMoment_add_two` : the recurrence
  `I_{L+2}(p) = (p-L-1)/(p+L+1) I_L(p)`.
* `Lyons.Converse.cosMoment_two_mul_add_one` : the odd moments as a product.
* `Lyons.Converse.cosMoment_neg` : `I_{2m+3}(p) < 0` for `2m < p < 2m+2`.
* `Lyons.Converse.signedPowFourier_eq_cosMoment` : `Γ_K(p) = (2/π) I_K(p)` for
  odd `K`.
* `Lyons.Converse.signedPowFourier_neg` : `Γ_{2m+3}(p) < 0` for `2m < p < 2m+2`.

The Riemann-sum step that follows is not here: it is carried as the explicit
hypothesis `Lyons.Converse.RiemannSumAssumption`, because Mathlib's box-integral
Riemann sums require a continuous integrand, and `J_p ∘ cos` is discontinuous
exactly at `p = 1`.
-/

open MeasureTheory Set intervalIntegral

open scoped Real

namespace Lyons.Converse

variable {p : ℝ}

/-! ### Continuity of the integrands -/

/-- For a nonnegative real exponent `q`, the power `t ↦ (cos t)^q` is continuous
on all of `ℝ`, including where the cosine vanishes: `Real.rpow` is continuous at
a zero base as soon as the exponent is nonnegative. -/
theorem continuous_cos_rpow {q : ℝ} (hq : 0 ≤ q) : Continuous fun t : ℝ => Real.cos t ^ q :=
  Real.continuous_cos.rpow_const fun _ => Or.inr hq

/-- The integrand of `cosMoment`, at a real frequency, is continuous. -/
theorem continuous_cos_rpow_mul_cos {q : ℝ} (hq : 0 ≤ q) (c : ℝ) :
    Continuous fun t : ℝ => Real.cos t ^ q * Real.cos (c * t) :=
  (continuous_cos_rpow hq).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- The `rpow` addition rule in the one shape used repeatedly below:
`x^{p-1} * x = x^p` for `x ≥ 0` and `p ≠ 0`.  The hypothesis `p ≠ 0` is what
makes it hold at `x = 0`, where `0^{p-1} * 0 = 0 = 0^p`. -/
theorem rpow_sub_one_mul_self (hp : p ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (p - 1) * x = x ^ p := by
  have h : x ^ (p - 1 + 1) = x ^ (p - 1) * x ^ (1 : ℝ) :=
    Real.rpow_add' hx (by simpa using hp)
  simpa using h.symm

/-! ### The cosine moments -/

/-- The cosine moment `I_K(p) = ∫_0^{π/2} (cos t)^{p-1} cos (K t) dt`. -/
@[lyons_tag "def_Ik"]
noncomputable def cosMoment (p : ℝ) (K : ℤ) : ℝ :=
  ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (p - 1) * Real.cos ((K : ℝ) * t)

private theorem zero_le_pi_div_two : (0 : ℝ) ≤ π / 2 := by positivity

private theorem cos_nonneg_of_uIcc {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) (π / 2)) : 0 ≤ Real.cos t := by
  rw [uIcc_of_le zero_le_pi_div_two] at ht
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩

/-- The first moment is positive.

The proof rewrites `I_1(p)` as `∫_0^{π/2} (cos t)^p dt`, whose integrand is
continuous, nonnegative, and strictly positive on `(0, π/2)`. -/
@[lyons_tag "lem_I1_pos"]
theorem cosMoment_one_pos (hp : 1 ≤ p) : 0 < cosMoment p 1 := by
  have hp0 : p ≠ 0 := by positivity
  have hrw : cosMoment p 1 = ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ p := by
    rw [cosMoment]
    refine integral_congr fun t ht => ?_
    simpa using rpow_sub_one_mul_self hp0 (cos_nonneg_of_uIcc ht)
  rw [hrw]
  refine intervalIntegral_pos_of_pos_on
    ((continuous_cos_rpow (by linarith : (0 : ℝ) ≤ p)).intervalIntegrable _ _) ?_ (by positivity)
  intro t ht
  exact Real.rpow_pos_of_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩) p

/-! ### Integration by parts -/

/-- The derivative of `s ↦ (cos s)^p` is `-p (cos s)^{p-1} sin s`.

No case distinction on `cos t = 0` is needed, and no restriction to `[0, π/2]`:
`Real.hasDerivAt_rpow_const` applies at a zero base as soon as `1 ≤ p`. -/
@[lyons_tag "lem_cos_rpow_deriv"]
theorem hasDerivAt_cos_rpow (hp : 1 ≤ p) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos s ^ p) (-(p * Real.cos t ^ (p - 1) * Real.sin t)) t :=
  ((Real.hasDerivAt_cos t).rpow_const (Or.inr hp)).congr_deriv (by ring)

/-- The derivative of `s ↦ sin (c s)`. -/
private theorem hasDerivAt_sin_const_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (c * s)) (c * Real.cos (c * t)) t := by
  have h : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  simpa [mul_comm] using h.sin

/-- `cos((l+2)t) - cos(lt) = -2 sin((l+1)t) sin t`, stated for a real `l` rather
than only an integer one. -/
@[lyons_tag "lem_cos_identity"]
theorem cos_add_two_mul_sub_cos_mul (l t : ℝ) :
    Real.cos ((l + 2) * t) - Real.cos (l * t) = -2 * Real.sin ((l + 1) * t) * Real.sin t := by
  rw [Real.cos_sub_cos, show ((l + 2) * t + l * t) / 2 = (l + 1) * t by ring,
    show ((l + 2) * t - l * t) / 2 = t by ring]

/-- Integration by parts for the moments.

The parts are `u(s) = (cos s)^p` and `v(s) = sin((L+1)s)`; both boundary terms
vanish, `u(π/2) = 0^p = 0` because `p > 0`, and `v(0) = 0`. -/
@[lyons_tag "lem_Ik_ibp"]
theorem cosMoment_sub_eq (hp : 1 ≤ p) (L : ℤ) :
    cosMoment p (L + 2) - cosMoment p L =
      -(2 * ((L : ℝ) + 1) / p) *
        ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ p * Real.cos (((L : ℝ) + 1) * t) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hpne : p ≠ 0 := hp0.ne'
  have hq : (0 : ℝ) ≤ p - 1 := by linarith
  set c : ℝ := (L : ℝ) + 1 with hc
  set C : ℝ := ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ p * Real.cos (c * t) with hC
  set S : ℝ := ∫ t in (0 : ℝ)..(π / 2),
    Real.cos t ^ (p - 1) * Real.sin t * Real.sin (c * t) with hS
  -- The difference of the two moments is a single integral.
  have hdiff : cosMoment p (L + 2) - cosMoment p L = -2 * S := by
    rw [cosMoment, cosMoment, ← integral_sub
      ((continuous_cos_rpow_mul_cos hq _).intervalIntegrable _ _)
      ((continuous_cos_rpow_mul_cos hq _).intervalIntegrable _ _), hS,
      ← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    have h := cos_add_two_mul_sub_cos_mul (L : ℝ) t
    push_cast
    rw [hc]
    linear_combination (Real.cos t ^ (p - 1)) * h
  -- Integration by parts relates `C` and `S`.
  have hu' : Continuous fun s : ℝ => -(p * Real.cos s ^ (p - 1) * Real.sin s) :=
    ((continuous_const.mul (continuous_cos_rpow hq)).mul Real.continuous_sin).neg
  have hv' : Continuous fun s : ℝ => c * Real.cos (c * s) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hibp := integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => Real.cos s ^ p)
    (u' := fun s : ℝ => -(p * Real.cos s ^ (p - 1) * Real.sin s))
    (v := fun s : ℝ => Real.sin (c * s)) (v' := fun s : ℝ => c * Real.cos (c * s))
    (a := 0) (b := π / 2)
    (fun x _ => hasDerivAt_cos_rpow hp x) (fun x _ => hasDerivAt_sin_const_mul c x)
    (hu'.intervalIntegrable _ _) (hv'.intervalIntegrable _ _)
  have e1 : (∫ x in (0 : ℝ)..(π / 2), Real.cos x ^ p * (c * Real.cos (c * x))) = c * C := by
    rw [hC, ← intervalIntegral.integral_const_mul]
    exact integral_congr fun x _ => by ring
  have e2 : (∫ x in (0 : ℝ)..(π / 2),
      (-(p * Real.cos x ^ (p - 1) * Real.sin x)) * Real.sin (c * x)) = -(p * S) := by
    rw [hS, show -(p * ∫ x in (0 : ℝ)..(π / 2),
        Real.cos x ^ (p - 1) * Real.sin x * Real.sin (c * x)) =
      ∫ x in (0 : ℝ)..(π / 2), (-p) * (Real.cos x ^ (p - 1) * Real.sin x * Real.sin (c * x)) from
        by rw [intervalIntegral.integral_const_mul]; ring]
    exact integral_congr fun x _ => by ring
  rw [e1, e2, Real.cos_pi_div_two, Real.zero_rpow hpne, mul_zero, Real.sin_zero] at hibp
  have key : c * C = p * S := by linear_combination hibp
  rw [hdiff, show S = c * C / p from by rw [eq_div_iff hpne]; linear_combination -key]
  ring

/-- The remaining integral is the sum of two moments. -/
@[lyons_tag "lem_prod_to_sum"]
theorem two_mul_integral_cos_rpow_mul_cos (hp : 1 ≤ p) (L : ℤ) :
    2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ p * Real.cos (((L : ℝ) + 1) * t) =
      cosMoment p (L + 2) + cosMoment p L := by
  have hp0 : p ≠ 0 := by positivity
  have hq : (0 : ℝ) ≤ p - 1 := by linarith
  rw [cosMoment, cosMoment, ← integral_add
    ((continuous_cos_rpow_mul_cos hq _).intervalIntegrable _ _)
    ((continuous_cos_rpow_mul_cos hq _).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  refine integral_congr fun t ht => ?_
  have hcos : 0 ≤ Real.cos t := cos_nonneg_of_uIcc ht
  have h1 : Real.cos t ^ (p - 1) * Real.cos t = Real.cos t ^ p := rpow_sub_one_mul_self hp0 hcos
  have h2 := Real.two_mul_cos_mul_cos t (((L : ℝ) + 1) * t)
  rw [show t - ((L : ℝ) + 1) * t = -((L : ℝ) * t) by ring,
    show t + ((L : ℝ) + 1) * t = ((L : ℝ) + 2) * t by ring, Real.cos_neg] at h2
  push_cast
  rw [← h1]
  linear_combination (Real.cos t ^ (p - 1)) * h2

/-- The moment recurrence `I_{L+2}(p) = (p-L-1)/(p+L+1) I_L(p)`.  The hypothesis
`0 ≤ L` is used only to know that the denominator `p + L + 1` is nonzero. -/
@[lyons_tag "lem_Ik_recurrence"]
theorem cosMoment_add_two (hp : 1 ≤ p) {L : ℤ} (hL : 0 ≤ L) :
    cosMoment p (L + 2) = (p - (L : ℝ) - 1) / (p + (L : ℝ) + 1) * cosMoment p L := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hden : 0 < p + (L : ℝ) + 1 := by linarith
  have h1 := cosMoment_sub_eq hp L
  have h2 := two_mul_integral_cos_rpow_mul_cos hp L
  have h3 : p * (cosMoment p (L + 2) - cosMoment p L) =
      -(((L : ℝ) + 1) * (cosMoment p (L + 2) + cosMoment p L)) := by
    calc p * (cosMoment p (L + 2) - cosMoment p L)
        = p * (-(2 * ((L : ℝ) + 1) / p) *
            ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ p * Real.cos (((L : ℝ) + 1) * t)) := by
          rw [h1]
      _ = -(((L : ℝ) + 1) *
            (2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ p * Real.cos (((L : ℝ) + 1) * t))) := by
          field_simp
      _ = -(((L : ℝ) + 1) * (cosMoment p (L + 2) + cosMoment p L)) := by rw [h2]
  rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
  linear_combination h3

/-- The odd moments as a product. -/
@[lyons_tag "lem_Ik_product"]
theorem cosMoment_two_mul_add_one (hp : 1 ≤ p) (M : ℕ) :
    cosMoment p (2 * (M : ℤ) + 1) =
      cosMoment p 1 * ∏ l ∈ Finset.Icc 1 M, (p - 2 * (l : ℝ)) / (p + 2 * (l : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hL : (0 : ℤ) ≤ 2 * (M : ℤ) + 1 := by positivity
    have hstep : cosMoment p (2 * ((M : ℕ) + 1 : ℤ) + 1) =
        (p - 2 * ((M : ℝ) + 1)) / (p + 2 * ((M : ℝ) + 1)) * cosMoment p (2 * (M : ℤ) + 1) := by
      rw [show 2 * ((M : ℕ) + 1 : ℤ) + 1 = (2 * (M : ℤ) + 1) + 2 by ring,
        cosMoment_add_two hp hL]
      push_cast
      ring_nf
    rw [show ((M + 1 : ℕ) : ℤ) = ((M : ℤ) + 1) by push_cast; ring, hstep, ih,
      Finset.prod_Icc_succ_top (Nat.le_add_left 1 M)]
    push_cast
    ring

/-- The negative odd moment: for `2m < p < 2m+2` the moment `I_{2m+3}(p)` is
negative, because exactly one factor of the product is. -/
@[lyons_tag "lem_Ik_neg"]
theorem cosMoment_neg {m : ℕ} (hp : 1 ≤ p) (hlb : 2 * (m : ℝ) < p) (hub : p < 2 * (m : ℝ) + 2) :
    cosMoment p (2 * (m : ℤ) + 3) < 0 := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  rw [show (2 : ℤ) * (m : ℤ) + 3 = 2 * ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring,
    cosMoment_two_mul_add_one hp]
  refine mul_neg_of_pos_of_neg (cosMoment_one_pos hp) ?_
  rw [Finset.prod_Icc_succ_top (Nat.le_add_left 1 m)]
  refine mul_neg_of_pos_of_neg (Finset.prod_pos fun l hl => ?_) ?_
  · have hlm : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hl).2
    have h1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    exact div_pos (by linarith) (by linarith)
  · exact div_neg_of_neg_of_pos (by push_cast; linarith) (by push_cast; linarith)

/-! ### The Fourier coefficient -/

/-- The Fourier coefficient `Γ_K(p) = (1/2π) ∫_0^{2π} J_p(cos t) cos(K t) dt`.
The letter `Γ` is used rather than `γ`, which is already spent on a block
power. -/
@[lyons_tag "def_gamma_K"]
noncomputable def signedPowFourier (p : ℝ) (K : ℤ) : ℝ :=
  (1 / (2 * π)) * ∫ t in (0 : ℝ)..(2 * π), signedPow p (Real.cos t) * Real.cos ((K : ℝ) * t)

/-- `J_p ∘ cos` times a cosine is interval integrable on every interval: it is
measurable and bounded by `1`.  It is *not* continuous — at `p = 1` it jumps
where the cosine vanishes — so the usual continuity route is unavailable and the
bound has to be used instead. -/
theorem intervalIntegrable_signedPow_cos (hp : 1 ≤ p) (c a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => signedPow p (Real.cos t) * Real.cos (c * t)) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne ?_ (M := 1)
    (Filter.Eventually.of_forall fun t => ?_)
  · exact (((measurable_signedPow hp).comp Real.measurable_cos).mul
      (Real.measurable_cos.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    calc |signedPow p (Real.cos t)| * |Real.cos (c * t)| ≤ 1 * 1 :=
          mul_le_mul (abs_signedPow_le_one hp (Real.abs_cos_le_one t))
            (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- For odd `K`, `Γ_K(p) = (2/π) I_K(p)`.

The proof folds `[0, 2π]` onto `[0, π]` by `t ↦ 2π - t`, then `[0, π]` onto
`[0, π/2]` by `t ↦ π - t` — where the two sign changes, from `J_p` being odd and
from `K` being odd, cancel — and finally identifies the integrand with that of
`cosMoment` on `(0, π/2)`, where the cosine is positive.  The two integrands may
differ at the single point `π/2`, which has measure zero. -/
@[lyons_tag "lem_gamma_eq_I"]
theorem signedPowFourier_eq_cosMoment (hp : 1 ≤ p) {K : ℤ} (hK : Odd K) :
    signedPowFourier p K = 2 / π * cosMoment p K := by
  set g : ℝ → ℝ := fun t => signedPow p (Real.cos t) * Real.cos ((K : ℝ) * t) with hg
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    intervalIntegrable_signedPow_cos hp _ a b
  -- Step 1: fold `[0, 2π]` onto `[0, π]`.
  have hsym1 : ∀ t : ℝ, g (2 * π - t) = g t := by
    intro t
    have h1 : Real.cos (2 * π - t) = Real.cos t := by
      simp [Real.cos_two_pi_sub]
    have h2 : Real.cos ((K : ℝ) * (2 * π - t)) = Real.cos ((K : ℝ) * t) := by
      rw [show (K : ℝ) * (2 * π - t) = (K : ℝ) * (2 * π) - (K : ℝ) * t by ring]
      exact Real.cos_int_mul_two_pi_sub ((K : ℝ) * t) K
    simp only [hg, h1, h2]
  have s1 : (∫ t in (0 : ℝ)..(2 * π), g t) = 2 * ∫ t in (0 : ℝ)..π, g t := by
    have hsplit := integral_add_adjacent_intervals (hint 0 π) (hint π (2 * π))
    have hfold : (∫ t in π..(2 * π), g t) = ∫ t in (0 : ℝ)..π, g t := by
      have h := integral_comp_sub_left (a := (0 : ℝ)) (b := π) g (2 * π)
      rw [show 2 * π - π = π by ring, sub_zero] at h
      rw [← h]
      exact integral_congr fun t _ => hsym1 t
    rw [← hsplit, hfold]
    ring
  -- Step 2: fold `[0, π]` onto `[0, π/2]`.
  have hsym2 : ∀ t : ℝ, g (π - t) = g t := by
    intro t
    have h1 : Real.cos (π - t) = -Real.cos t := Real.cos_pi_sub t
    have h2 : Real.cos ((K : ℝ) * (π - t)) = -Real.cos ((K : ℝ) * t) := by
      rw [show (K : ℝ) * (π - t) = (K : ℝ) * π - (K : ℝ) * t by ring,
        Real.cos_int_mul_pi_sub ((K : ℝ) * t) K, hK.neg_one_zpow]
      ring
    simp only [hg, h1, h2, signedPow_neg]
    ring
  have s2 : (∫ t in (0 : ℝ)..π, g t) = 2 * ∫ t in (0 : ℝ)..(π / 2), g t := by
    have hsplit := integral_add_adjacent_intervals (hint 0 (π / 2)) (hint (π / 2) π)
    have hfold : (∫ t in (π / 2)..π, g t) = ∫ t in (0 : ℝ)..(π / 2), g t := by
      have h := integral_comp_sub_left (a := (0 : ℝ)) (b := π / 2) g π
      rw [show π - π / 2 = π / 2 by ring, sub_zero] at h
      rw [← h]
      exact integral_congr fun t _ => hsym2 t
    rw [← hsplit, hfold]
    ring
  -- Step 3: identify the remaining integral with the moment.
  have s3 : (∫ t in (0 : ℝ)..(π / 2), g t) = cosMoment p K := by
    rw [cosMoment]
    refine integral_congr_uIoo ?_
    rw [uIoo_of_le zero_le_pi_div_two]
    intro t ht
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    simp only [hg, signedPow_of_pos hcos]
  rw [signedPowFourier, s1, s2, s3]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The Fourier coefficient is negative at the frequency `K = 2m+3`. -/
@[lyons_tag "lem_gamma_neg"]
theorem signedPowFourier_neg {m : ℕ} (hp : 1 ≤ p) (hlb : 2 * (m : ℝ) < p)
    (hub : p < 2 * (m : ℝ) + 2) : signedPowFourier p (2 * (m : ℤ) + 3) < 0 := by
  have hodd : Odd (2 * (m : ℤ) + 3) := ⟨(m : ℤ) + 1, by ring⟩
  rw [signedPowFourier_eq_cosMoment hp hodd]
  exact mul_neg_of_pos_of_neg (by positivity) (cosMoment_neg hp hlb hub)

end Lyons.Converse
