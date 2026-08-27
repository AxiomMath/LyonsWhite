/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Analysis.RiemannSum
import Lyons.Converse.DistDeriv
import Lyons.Converse.EnergyFormula
import Lyons.Converse.SandwichLimit
import Lyons.Objective.TheoremC
import Lyons.Walk.Realization

/-!
# Failure of rate-monotonicity for an inversion extension of a cyclic group

The assembly that turns the positive energy of the regularised test element into
an actual violation of `Lyons.RateMonotonic`, and from it the failure of
rate-monotonicity on the dihedral groups.

## The two bridges

Everything upstream of this file speaks of the *energy* and of `reflDistPow`;
`Lyons.RateMonotonic` speaks of `Lyons.distToUniform`. Two small lemmas connect
them, and they are the only genuinely new content here; the rest is
bookkeeping.

* `Lyons.Converse.distToUniform_eq_reflDistPow_rpow` — `d_p^ν(t)` is the `p`-th
  root of `reflDistPow`. Both sides are the same sum: `Lyons.co_centeredElt`
  says a coefficient of `Lyons.centeredElt` *is* the centered transition
  function, which is what `Lyons.distToUniform` sums.
* `Lyons.Converse.setOrb_self` — moving a rate onto an orbit to the value it
  already has changes nothing. This is `λ°[1↦α] = λ°`, and it is what lets the
  derivative of `Lyons.Converse.reflDistPow` at `α` be read as a statement about
  `λ°` itself.

## Why the orbit is a single point

`Lyons.invOrbit s` is `{s, s⁻¹}`, and at `z = 0` a reflection is its own inverse
(`Lyons.Converse.refl_inv_self`), so the orbit of `τ` is `{τ}`. That is what
makes `setOrb` at `τ` a change in one coordinate, and it is why `λ°[1↦β]` may be
read as "`λ°` with its value at `τ` replaced".
-/

open Finset

namespace Lyons.Converse

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **The distance to stationarity is the `p`-th root of `reflDistPow`.**

`Lyons.distToUniform` sums `|heatCoeffReal ν t g - |G|⁻¹|^p` and takes the `p`-th
root; `Lyons.Converse.reflDistPow` sums `|co (centeredElt ν t) g|^p`. By
`Lyons.co_centeredElt` the two summands are literally the same real number, so
the only difference between the two notions is the outer root. -/
theorem distToUniform_eq_reflDistPow_rpow (lam0 : RateFn G) {s : G} (hs1 : s ≠ 1)
    {α : ℝ} (hα : 0 ≤ α) (t p : ℝ) :
    distToUniform p (lam0.addOrbit hs1 hα) t
      = (reflDistPow lam0 s t p α) ^ p⁻¹ := by
  rw [distToUniform, reflDistPow_eq lam0 hs1 hα]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [co_centeredElt, centeredHeatCoeffReal]

omit [Fintype G] in
/-- **Setting a rate on an orbit to the value it already has does nothing.**

This is `λ°[1↦α] = λ°`. The orbit of `s` is `{s, s⁻¹}` and a rate function is
symmetric, so if it already takes the value `α` at `s` it takes it on the whole
orbit; off the orbit `setOrb` is the identity by construction. -/
theorem setOrb_self (lam : RateFn G) {s : G} (hs1 : s ≠ 1) {α : ℝ} (hα : 0 ≤ α)
    (hval : lam s = α) : lam.setOrb hs1 hα = lam := by
  refine DFunLike.ext _ _ fun g => ?_
  rw [RateFn.setOrb_apply]
  by_cases h : g ∈ invOrbit s
  · rw [if_pos h]
    rcases mem_invOrbit.mp h with rfl | rfl
    · exact hval.symm
    · rw [lam.symm, hval]
  · rw [if_neg h]

/-- **A positive number strictly below every member of a finite nonempty family
of positive numbers, and below a given bound.**

This is needed twice below: `ε` must be below `ε₀` *and* below
`min_j |cos(2πj/n)|`, and `ς` below `ς₀` *and* below `min_g |(ξ_{n,K,ε})_g|`. The
minimum of finitely many positive numbers is positive, so taking half of the
smaller of the two makes both inequalities strict at once.

Nonemptiness is taken as an explicit witness `i₀` rather than a `[Nonempty ι]`
instance. -/
theorem exists_pos_lt_of_finite {ι : Type*} [Finite ι] (i₀ : ι) (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) {c : ℝ} (hc : 0 < c) :
    ∃ b : ℝ, 0 < b ∧ b < c ∧ ∀ i, b < f i := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  let _ : Fintype ι := Fintype.ofFinite ι
  set m : ℝ := Finset.univ.inf' Finset.univ_nonempty f with hm
  have hm0 : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    exact fun i _ => hf i
  refine ⟨min c m / 2, by positivity, ?_, fun i => ?_⟩
  · have : min c m ≤ c := min_le_left _ _
    linarith [hm0, hc, min_le_left c m, min_le_right c m]
  · have hle : m ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
    have : min c m ≤ m := min_le_right _ _
    have hmin0 : 0 < min c m := lt_min hc hm0
    linarith

/-! ### The parameters

`K` and `n` from the negative character sum, then `ε` and `ς` small enough that
the energy is positive *and* every coefficient is nonzero. The two smallness
conditions are independent — one comes from a limit, the other from a finite
minimum — which is why `exists_pos_lt_of_finite` handles both at once. -/

set_option maxHeartbeats 1000000 in
-- The two character sums are large terms, and `exists_neg_char_sum`'s conclusion
-- has to be matched cast for cast against `exists_energy_testElement_pos`'s
-- hypothesis; unifying them exceeds the default budget.
/-- An odd `n`, a `K`, and parameters `ε, ς > 0` for which the regularised test
element has positive energy and no vanishing coefficient.

Bundled as one lemma because the four parameters are chosen in sequence and every
later choice depends on the earlier ones; splitting it would mean threading `n`
through a dependent existential four times. -/
private theorem exists_params {p : ℝ} (hp : 1 < p)
    (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * m) :
    ∃ (n : ℕ) (_ : NeZero n) (K : ℤ) (ε ς : ℝ),
      0 < ς ∧
        (∀ g : InvExt (ZMod n) 0, co (regTestElement n K ε ς) g ≠ 0) ∧
        0 < energy p (regTestElement n K ε ς) (InvExt.b : InvExt (ZMod n) 0) ∧
        IsPos (regTestElement n K ε ς) ∧
        regTestElement n K ε ς * uniform (InvExt (ZMod n) 0) = 0 ∧
        IsPosDefOffConst (regTestElement n K ε ς) := by
  -- Step 1: `K` and `n` with a negative character sum.
  obtain ⟨Knat, l, hKodd, hK3, hKn, hsum⟩ := exists_neg_char_sum hp hp2
  -- `n` is kept as the literal `2 * l + 1` rather than abbreviated. `set` does
  -- not reach inside the `((2 * l + 1 : ℕ) : ℝ)` casts of `hsum` — the ℕ
  -- expression there elaborates through a different instance path — so
  -- abbreviating splits the goal's index type from the hypothesis's.
  have hn0 : NeZero (2 * l + 1) := ⟨by omega⟩
  have hodd : Odd (2 * l + 1) := ⟨l, by omega⟩
  have hK : 2 ≤ (Knat : ℤ) := by exact_mod_cast le_trans (by norm_num) hK3
  have hn : 2 * (Knat : ℤ) < ((2 * l + 1 : ℕ) : ℤ) := by exact_mod_cast hKn
  have hneg : ∑ j : ZMod (2 * l + 1),
      signedPow p (Real.cos (2 * Real.pi * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ)))
        * Real.cos (2 * Real.pi * ((Knat : ℤ) * (j.val : ℤ) : ℝ)
            / ((2 * l + 1 : ℕ) : ℝ)) < 0 :=
    calc ∑ j : ZMod (2 * l + 1),
            signedPow p (Real.cos (2 * Real.pi * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ)))
              * Real.cos (2 * Real.pi * ((Knat : ℤ) * (j.val : ℤ) : ℝ)
                  / ((2 * l + 1 : ℕ) : ℝ))
        = ∑ j : ZMod (2 * l + 1),
            signedPow p (Real.cos (2 * Real.pi * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ)))
              * Real.cos (2 * Real.pi * ((Knat : ℝ) * (j.val : ℝ))
                  / ((2 * l + 1 : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun j _ => by push_cast; ring_nf
      _ < 0 := hsum
  -- Step 2: `ε`.
  obtain ⟨ε₀, hε₀, hEp⟩ := exists_energy_testElement_pos hK hn hodd p hneg
  have hcospos : ∀ j : ZMod (2 * l + 1),
      0 < |Real.cos (2 * Real.pi * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ))| := by
    intro j
    refine abs_pos.mpr ?_
    have h := cos_two_pi_div_ne_zero hodd (j.val : ℤ)
    rwa [show (((j.val : ℤ)) : ℝ) = (j.val : ℝ) by push_cast; ring] at h
  obtain ⟨ε, hε0, hεlt, hεcos⟩ := exists_pos_lt_of_finite (0 : ZMod (2 * l + 1))
    (fun j : ZMod (2 * l + 1) =>
      |Real.cos (2 * Real.pi * (j.val : ℝ) / ((2 * l + 1 : ℕ) : ℝ))|) hcospos hε₀
  have hεpos : 0 < energy p (testElement (2 * l + 1) (Knat : ℤ) ε)
      (InvExt.b : InvExt (ZMod (2 * l + 1)) 0) :=
    hEp ε hε0 hεlt
  have hne : ∀ g : InvExt (ZMod (2 * l + 1)) 0,
      co (testElement (2 * l + 1) (Knat : ℤ) ε) g ≠ 0 :=
    coeff_testElement_ne_zero (Knat : ℤ) hε0 hεcos
  -- Step 3: `ς`.
  obtain ⟨ς₀, hς₀, hEpreg⟩ :=
    exists_energy_regTestElement_pos hK hn hε0.le hp.le hne hεpos
  obtain ⟨ς, hς0, hςlt, hςco⟩ := exists_pos_lt_of_finite
    (1 : InvExt (ZMod (2 * l + 1)) 0)
    (fun g : InvExt (ZMod (2 * l + 1)) 0 =>
      |co (testElement (2 * l + 1) (Knat : ℤ) ε) g|)
    (fun g => abs_pos.mpr (hne g)) hς₀
  exact ⟨2 * l + 1, hn0, (Knat : ℤ), ε, ς, hς0,
    coeff_regTestElement_ne_zero (Knat : ℤ) hς0 hςco,
    hEpreg ς hς0 hςlt, isPos_regTestElement hK hn hε0.le hς0.le,
    regTestElement_mul_uniform hK hn ε ς,
    isPosDefOffConst_regTestElement hK hn hε0.le hς0⟩

/-! ### Realisation, differentiation, and the two rate collections -/

/-- For a positive element `x` killed by the uniform element and positive
definite off the constants, there is a generating symmetric rate collection whose
centered heat element at time `1` is a positive multiple of `x`, with the energy
scaled by `Lyons.Converse.energy_smul`.

Stated for an arbitrary finite group and an arbitrary `x`, since neither
`exists_rate_centeredHeat_eq` nor `energy_smul` looks at the inversion
extension. -/
private theorem exists_rate_energy_pos {H : Type*} [Group H] [Fintype H]
    [DecidableEq H] {x : MonoidAlgebra ℝ H} (hx : IsPos x)
    (hxu : x * uniform H = 0) (hpd : IsPosDefOffConst x) (p : ℝ) (c : H)
    (hEp : 0 < energy p x c) (hne : ∀ g : H, co x g ≠ 0) :
    ∃ (lam : H → ℝ) (hlam : IsSymmRate lam),
      Generating lam ∧ (∀ s : H, s ≠ 1 → 0 < lam s) ∧
        0 < energy p (centeredElt hlam.toRateFn 1) c ∧
        (∀ g : H, co (centeredElt hlam.toRateFn 1) g ≠ 0) := by
  obtain ⟨lam, hlam, rho, hgen, hpos, hrho, hcoeff⟩ :=
    exists_rate_centeredHeat_eq hx hxu hpd
  have hexp : (0 : ℝ) < Real.exp (-rho) := Real.exp_pos _
  -- The centered heat element *is* `exp(-ρ) • x`, coefficientwise.
  have helt : centeredElt hlam.toRateFn 1 = Real.exp (-rho) • x := by
    refine co_injective fun g => ?_
    rw [co_centeredElt, co_smul, hcoeff g]
  refine ⟨lam, hlam, hgen, hpos, ?_, fun g => ?_⟩
  · rw [helt, energy_smul p hx c hexp]
    exact mul_pos (Real.rpow_pos_of_pos hexp p) hEp
  · rw [helt, co_smul]
    exact mul_ne_zero hexp.ne' (hne g)

/-- **Failure of rate-monotonicity for an inversion extension of a cyclic
group.**

The assembly, in order: `exists_params` supplies the parameters `n, K, ε, ς`;
`exists_rate_energy_pos` the realisation and the energy scaling;
`Lyons.Converse.hasDerivAt_reflDistPow_setOrb_refl` with
`Lyons.exists_gt_of_hasDerivAt_pos` make the derivative `p · 𝓔_p > 0`, so that
some `β > α` raises the power sum; and what is left is the construction of `μ`
and the comparison of the two distances through
`distToUniform_eq_reflDistPow_rpow`.

The hypothesis is `p > 1` rather than `p ≥ 1`, inherited from
`Lyons.Converse.exists_neg_char_sum`, whose Riemann-sum input is only available
for `p > 1`.

The cyclic group is `ZMod n`, and `z = 1`, `d = 1` become `z = 0`, `d = 0`, so
`τ` is `Lyons.InvExt.b = InvExt.refl 0`. The `NeZero n` instance travels inside
the existential, as in `Lyons.exists_not_rateMonotonic_dihedral_of_invExt`:
`RateMonotonic` needs the group finite, and that instance is the condition
`n ≥ 1`. -/
@[lyons_tag "prop_converse_cyclic"]
theorem exists_not_rateMonotonic_invExt {p : ℝ} (hp : 1 < p)
    (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * m) :
    ∃ m : ℕ, ∃ _ : NeZero m, ¬ RateMonotonic (InvExt (ZMod m) 0) p := by
  classical
  obtain ⟨n, hn0, K, ε, ς, hς0, hcone, hEp, hxpos, hxu, hpd⟩ := exists_params hp hp2
  refine ⟨n, hn0, ?_⟩
  set x : MonoidAlgebra ℝ (InvExt (ZMod n) 0) := regTestElement n K ε ς with hx_def
  set τ : InvExt (ZMod n) 0 := InvExt.refl 0 with hτ_def
  have hτb : (InvExt.b : InvExt (ZMod n) 0) = τ := rfl
  rw [hτb] at hEp
  -- Step 4: realise `x` as a centered heat element, up to a positive scalar.
  obtain ⟨lam, hlam, hgen, hlampos, hEnergy, hcone'⟩ :=
    exists_rate_energy_pos hxpos hxu hpd p τ hEp hcone
  set ν : RateFn (InvExt (ZMod n) 0) := hlam.toRateFn with hν_def
  have hτ1 : τ ≠ 1 := refl_ne_one 0
  -- `α` is the rate at `τ`, and `λ°[1↦α] = λ°`.
  set α : ℝ := ν τ with hα_def
  have hα : 0 ≤ α := ν.nonneg τ
  have hαpos : 0 < α := by
    rw [hα_def, hν_def, IsSymmRate.toRateFn_apply, if_neg hτ1]
    exact hlampos τ hτ1
  have hset : ν.setOrb hτ1 hα = ν := setOrb_self ν hτ1 hα rfl
  -- The base rate: `λ°` with the orbit of `τ` zeroed. Named before Step 5 so the
  -- derivative, `hβgt` and the two bridge applications all speak of one term.
  set lam0 : RateFn (InvExt (ZMod n) 0) := ν.setOrb hτ1 (le_refl (0 : ℝ))
    with hlam0_def
  -- Step 5: differentiate the power sum at `α`.
  have hderivne : ∀ g : InvExt (ZMod n) 0,
      co (centeredElt (ν.setOrb hτ1 hα) 1) g ≠ 0 := by
    rw [hset]; exact hcone'
  have hderiv := hasDerivAt_reflDistPow_setOrb_refl (z := (0 : ZMod n)) rfl ν 0 1
    hα hp.le hderivne
  have hD : 0 < p * 1 * energy p (centeredElt (ν.setOrb hτ1 hα) 1) (InvExt.refl 0) := by
    rw [hset, mul_one]
    exact mul_pos (by linarith) hEnergy
  obtain ⟨β, hβα, hβgt⟩ := exists_gt_of_hasDerivAt_pos hderiv hD
  have hβ : 0 ≤ β := le_trans hα (le_of_lt hβα)
  -- Step 6: the two collections. `μ` raises the rate at `τ` to `β`.
  set mu : InvExt (ZMod n) 0 → ℝ := fun s => if s ∈ invOrbit τ then β else lam s
    with hmu_def
  -- `λ` takes the value `α` at `τ`, which is what makes `μ ≥ λ`.
  have hmu_apply : ∀ s, mu s = if s ∈ invOrbit τ then β else lam s := fun _ => rfl
  have hlamτ : lam τ = α := by
    rw [hα_def, hν_def, IsSymmRate.toRateFn_apply, if_neg hτ1]
  have hτinv : τ⁻¹ = τ := refl_inv_self rfl 0
  have hmusymm : IsSymmRate mu := by
    refine ⟨fun s => ?_, fun s => ?_⟩
    · rw [hmu_apply]
      by_cases h : s ∈ invOrbit τ
      · simpa [h] using hβ
      · simpa [h] using hlam.nonneg s
    · rw [hmu_apply, hmu_apply]
      by_cases h : s ∈ invOrbit τ
      · rw [if_pos (inv_mem_invOrbit h), if_pos h]
      · rw [if_neg fun hc => h (by simpa using inv_mem_invOrbit hc), if_neg h,
          hlam.symm]
  have hle : ∀ s, lam s ≤ mu s := by
    intro s
    rw [hmu_apply]
    by_cases h : s ∈ invOrbit τ
    · rw [if_pos h]
      rcases mem_invOrbit.mp h with rfl | rfl
      · rw [hlamτ]; exact hβα.le
      · rw [hτinv, hlamτ]; exact hβα.le
    · rw [if_neg h]
  -- Raising rates cannot shrink the support, so `μ` is still generating.
  have hgenmu : Generating mu := by
    rw [Generating, ← top_le_iff, ← hgen]
    exact Subgroup.closure_mono fun s hs => lt_of_lt_of_le hs (hle s)
  -- `μ° = λ°[1↦β]`: both are `β` on the orbit, `λ` off it, and `0` at `1`.
  have hmuset : hmusymm.toRateFn = ν.setOrb hτ1 hβ := by
    refine DFunLike.ext _ _ fun g => ?_
    rw [IsSymmRate.toRateFn_apply, RateFn.setOrb_apply, hν_def]
    by_cases h1 : g = 1
    · subst h1
      rw [if_pos rfl, if_neg (one_notMem_invOrbit hτ1),
        IsSymmRate.toRateFn_apply, if_pos rfl]
    · rw [if_neg h1, hmu_apply]
      by_cases h : g ∈ invOrbit τ
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, IsSymmRate.toRateFn_apply, if_neg h1]
  -- Step 7: compare the two distances through the two bridges.
  have hbridge : ∀ (γ : ℝ) (hγ : 0 ≤ γ),
      distToUniform p (ν.setOrb hτ1 hγ) 1
        = (reflDistPow lam0 τ 1 p γ) ^ p⁻¹ := by
    intro γ hγ
    rw [RateFn.setOrb_eq_addOrbit ν hτ1 hγ, ← hlam0_def]
    exact distToUniform_eq_reflDistPow_rpow _ hτ1 hγ 1 p
  have hpinv : 0 < p⁻¹ := by positivity
  have hnn : 0 ≤ reflDistPow lam0 τ 1 p α :=
    Finset.sum_nonneg fun g _ => Real.rpow_nonneg (abs_nonneg _) p
  have hstrict : distToUniform p ν 1 < distToUniform p hmusymm.toRateFn 1 := by
    have h1 : distToUniform p ν 1 = (reflDistPow lam0 τ 1 p α) ^ p⁻¹ := by
      conv_lhs => rw [← hset]
      exact hbridge α hα
    have h2 : distToUniform p hmusymm.toRateFn 1
        = (reflDistPow lam0 τ 1 p β) ^ p⁻¹ := by
      rw [hmuset]; exact hbridge β hβ
    rw [h1, h2]
    exact Real.rpow_lt_rpow hnn hβgt hpinv
  -- If `(G, p)` were rate-monotonic the two distances would be the other way.
  intro hmono
  have hcon := hmono lam mu hlam hmusymm hgen hgenmu hle 1 zero_le_one
  exact absurd hcon (not_le.mpr hstrict)

end Lyons.Converse

/-! ### Failure of rate-monotonicity on the dihedral group -/

namespace Lyons

/-- **Failure of rate-monotonicity away from even integers.**

This is `Lyons.exists_not_rateMonotonic_dihedral_of_invExt` applied to
`Lyons.Converse.exists_not_rateMonotonic_invExt`, and nothing else.

The hypothesis is `p > 1`, not `p ≥ 1`. It comes from
`Lyons.Converse.exists_neg_char_sum`, whose Riemann-sum input holds only for
`p > 1`: at `p = 1` the integrand `J_p ∘ cos` is the sign of the cosine,
discontinuous at `π/2` and `3π/2`, and the continuous Riemann-sum theorem it
rests on does not apply. Since `p = 1` is the `ℓ¹` metric, the gap is a real
one. -/
@[lyons_tag "thm_main_converse"]
theorem not_rateMonotonic_dihedral_of_not_even {p : ℝ} (hp : 1 < p)
    (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * m) :
    ∃ m : ℕ, ∃ _ : NeZero m, ¬ RateMonotonic (DihedralGroup m) p :=
  exists_not_rateMonotonic_dihedral_of_invExt
    (Converse.exists_not_rateMonotonic_invExt hp hp2)

end Lyons
