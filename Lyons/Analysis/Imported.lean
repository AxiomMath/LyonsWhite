/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Lyons.Meta.Tag

/-!
# Real-analysis inputs imported from Mathlib

Classical real-analysis inputs used below, each restated in the shape this
development needs and discharged from Mathlib.

Each declaration below earns its place in one of three ways.

* It *specialises*: the Mathlib statement is more general in a direction no
  consumer uses, and the specialisation removes bookkeeping at every call site
  (`pow_sum_mul_le_sum_mul_pow` fixes the convex function to an even power;
  `tendsto_intervalIntegral_of_dominated` fixes the dominating function to a
  constant and discharges its integrability).
* It *reshapes*: the content is Mathlib's but the arrangement is not
  (`integral_deriv_mul_eq_sub_integral` puts `∫ u' v` on the left where Mathlib
  puts `∫ u v'`; `le_of_deriv_nonpos` reads off the two endpoints of an
  `AntitoneOn`).
* It is not in Mathlib at all (`exists_gt_of_hasDerivAt_pos`, which needs
  differentiability at the single point `α` only, so no mean-value theorem
  applies).

The two cosine identities are in Mathlib verbatim, and are re-exported here so
that the Fourier computations that use them cite a `Lyons` name like every other
step.

## Main results

* `Lyons.two_mul_cos_mul_cos` : product to sum for cosines.
* `Lyons.cos_sub_cos` : difference of cosines.
* `Lyons.integral_deriv_mul_eq_sub_integral` : integration by parts on `[a, b]`.
* `Lyons.pow_sum_mul_le_sum_mul_pow` : Jensen's inequality for a finite convex
  combination and an even power.
* `Lyons.le_of_deriv_nonpos` : a nonpositive derivative on `[c, d]` forces
  `Φ d ≤ Φ c`.
* `Lyons.exists_gt_of_hasDerivAt_pos` : a positive derivative at `α` forces a
  larger value to the right of `α`.
* `Lyons.tendsto_intervalIntegral_of_dominated` : dominated convergence along
  `𝓝[T] 0` with a constant dominating function.
-/

open Filter MeasureTheory
open scoped Topology

namespace Lyons

/-! ### Trigonometric identities -/

/-- **Product to sum for cosines.** This is Mathlib's
`Real.two_mul_cos_mul_cos`, re-exported under a `Lyons` name so that the Fourier
computations that use it cite a declaration of this development rather than
reaching into `Real` directly. -/
@[lyons_tag "lem_ext_cos_prod"]
theorem two_mul_cos_mul_cos (A B : ℝ) :
    2 * Real.cos A * Real.cos B = Real.cos (A - B) + Real.cos (A + B) :=
  Real.two_mul_cos_mul_cos A B

/-- **Difference of cosines.** This is Mathlib's `Real.cos_sub_cos`, re-exported
for the same reason as `Lyons.two_mul_cos_mul_cos`. -/
@[lyons_tag "lem_ext_cos_sub_cos"]
theorem cos_sub_cos (A B : ℝ) :
    Real.cos A - Real.cos B = -2 * Real.sin ((A + B) / 2) * Real.sin ((A - B) / 2) :=
  Real.cos_sub_cos A B

/-! ### Integration by parts -/

/-- **Integration by parts on an interval.**

Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, with the two
factors exchanged: Mathlib solves for `∫ u v'` and this statement solves for
`∫ u' v`, which is the side the consumer starts from. Since both integrals occur
in Mathlib's identity, the exchange is a linear rearrangement and no analysis is
redone.

Two presentational deviations from Mathlib. The hypotheses are stated on
`Set.Icc a b` with `a ≤ b` rather than on `Set.uIcc a b`; and the codomain is
`ℝ` rather than a general normed algebra, which is all this development
integrates. -/
@[lyons_tag "lem_ext_ibp"]
theorem integral_deriv_mul_eq_sub_integral {a b : ℝ} (hab : a ≤ b) {u v u' v' : ℝ → ℝ}
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (u' t) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (v' t) t)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ t in a..b, u' t * v t = u b * v b - u a * v a - ∫ t in a..b, u t * v' t := by
  rw [← Set.uIcc_of_le hab] at hu hv
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  linarith

/-! ### Jensen's inequality -/

/-- **Jensen's inequality for a finite convex combination and an even power.**

Mathlib's `ConvexOn.map_sum_le`, fed the convexity of an even power supplied by
`Even.convexOn_pow`.

The exponent is an even natural number rather than a real `q ≥ 1`, and the
absolute values of the general statement are consequently absent: for even `q`
one has `t ^ q = |t| ^ q`. This is the only case any consumer needs, and it is
also the only case that *can* be used here. `Even.convexOn_pow` is convex on
`Set.univ`, whereas `convexOn_rpow` is convex only on `Set.Ici 0`; the function
this is applied to is a coefficient of the centered heat element, which is
negative wherever the walk sits below uniform, so a lemma restricted to the
nonnegative half-line would not apply at all.

Positivity of `q` is not needed: at `q = 0` both sides are `∑ κ x = 1`, so `hq`
is the only hypothesis on `q`. -/
@[lyons_tag "lem_ext_jensen"]
theorem pow_sum_mul_le_sum_mul_pow {ι : Type*} {s : Finset ι} {κ φ : ι → ℝ}
    (hκ₀ : ∀ x ∈ s, 0 ≤ κ x) (hκ₁ : ∑ x ∈ s, κ x = 1) {q : ℕ} (hq : Even q) :
    (∑ x ∈ s, κ x * φ x) ^ q ≤ ∑ x ∈ s, κ x * φ x ^ q := by
  have h := (Even.convexOn_pow (𝕜 := ℝ) hq).map_sum_le (t := s) (w := κ) (p := φ)
    hκ₀ hκ₁ fun x _ => Set.mem_univ (φ x)
  simpa [smul_eq_mul] using h

/-! ### Monotonicity from a sign condition on the derivative -/

/-- **A nonpositive derivative on `[c, d]` forces `Φ d ≤ Φ c`.**

Mathlib's `antitoneOn_of_deriv_nonpos`, evaluated at the two endpoints.

`Φ` is a function on all of `ℝ` rather than on `[c, d]`, with the two
hypotheses restricted to `Set.Icc c d`; that is the form in which every consumer
has a function on `[c, d]`. Mathlib's differentiability and sign
hypotheses live on `interior (Set.Icc c d)`, which the `Set.Icc c d` hypotheses
here subsume; asking for them on the closed interval costs nothing at the call
sites and lets `ContinuousOn Φ (Set.Icc c d)` be read off `hdiff` instead of
being a third hypothesis. -/
@[lyons_tag "lem_ext_mono_of_deriv"]
theorem le_of_deriv_nonpos {Φ : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hdiff : ∀ α ∈ Set.Icc c d, DifferentiableAt ℝ Φ α)
    (hderiv : ∀ α ∈ Set.Icc c d, deriv Φ α ≤ 0) : Φ d ≤ Φ c := by
  have hsub : interior (Set.Icc c d) ⊆ Set.Icc c d := interior_subset
  have hanti : AntitoneOn Φ (Set.Icc c d) :=
    antitoneOn_of_deriv_nonpos (convex_Icc c d)
      (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hdiff x (hsub hx)).differentiableWithinAt)
      fun x hx => hderiv x (hsub hx)
  exact hanti (Set.left_mem_Icc.mpr hcd) (Set.right_mem_Icc.mpr hcd) hcd

/-- **A positive derivative at a point forces a larger value to its right.**

Not available in Mathlib: `strictMono_of_hasDerivAt_pos` and the `StrictMonoOn`
family all need a derivative on a *set*, whereas the consumer — the final step of
`Lyons.not_rateMonotonic_dihedral_of_not_even` — has differentiability at the
single point `α` only: the nonvanishing hypothesis that makes `F` differentiable
is verified at `α` and nowhere else. So
the argument is run from the definition: the slope of `F` at `α` tends to `F'`,
hence is eventually positive on `𝓝[>] α`, and a positive slope with a positive
denominator is a positive increment.

Stated with `HasDerivAt F F' α` rather than `DifferentiableAt ℝ F α` together
with `0 < deriv F α`; the two are interchangeable via
`DifferentiableAt.hasDerivAt` and `HasDerivAt.deriv`, and the `HasDerivAt` form
is what the consumer produces. -/
@[lyons_tag "lem_gt_of_deriv_pos"]
theorem exists_gt_of_hasDerivAt_pos {F : ℝ → ℝ} {α F' : ℝ} (hF : HasDerivAt F F' α)
    (hF' : 0 < F') : ∃ β, α < β ∧ F α < F β := by
  have hslope : Tendsto (slope F α) (𝓝[>] α) (𝓝 F') :=
    hF.tendsto_slope.mono_left <| nhdsWithin_mono _ fun _ hx => ne_of_gt hx
  obtain ⟨β, hβslope, hβ⟩ :=
    ((hslope.eventually (eventually_gt_nhds hF')).and self_mem_nhdsWithin).exists
  refine ⟨β, hβ, ?_⟩
  rw [slope_def_field, div_pos_iff] at hβslope
  rcases hβslope with ⟨h₁, -⟩ | ⟨-, h₂⟩
  · linarith
  · linarith [sub_pos.mpr hβ]

/-! ### Dominated convergence -/

/-- **Dominated convergence along the filter `𝓝[T] 0`, with a constant bound.**

Mathlib's `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`,
with the dominating function taken to be the constant `C` — whose
`IntervalIntegrable` hypothesis is then discharged here by
`intervalIntegrable_const`, which is the whole point of the wrapper. The filter
`𝓝[T] (0 : ℝ)` is countably generated because `𝓝 (0 : ℝ)` is and an inf with a
principal filter preserves that, so Mathlib's instance argument is found
automatically.

The hypotheses are kept as weak as the proof allows.

* `T` is an arbitrary set of reals. For a set of positive reals with `0` in its
  closure, the restriction to `T` of the right-hand neighbourhood filter at `0`
  *is* `𝓝[T] 0`, so `T ⊆ Set.Ioi 0` is not assumed. Nor is `0 ∈ closure T`: it
  makes the conclusion informative (the filter is then `NeBot`) but is not
  needed to prove it.
* The pointwise hypotheses are almost-everywhere statements about the *open*
  interval `Set.Ioo a b` rather than the closed `[a, b]`. This is weaker, and it
  is the form the consumer produces, whose bound and limit are both established
  on the open interval. The endpoints are a null set, which is what lets them be
  dropped.
* `C ≥ 0` is not assumed; it follows from the bound as soon as `a < b`, and is
  never used. -/
@[lyons_tag "lem_ext_dominated"]
theorem tendsto_intervalIntegral_of_dominated {a b : ℝ} (hab : a ≤ b) {T : Set ℝ}
    {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hmeas : ∀ ς ∈ T, AEStronglyMeasurable (F ς) (volume.restrict (Set.Ioc a b)))
    (hbound : ∀ ς ∈ T, ∀ᵐ θ, θ ∈ Set.Ioo a b → |F ς θ| ≤ C)
    (hlim : ∀ᵐ θ, θ ∈ Set.Ioo a b → Tendsto (fun ς => F ς θ) (𝓝[T] 0) (𝓝 (f θ))) :
    Tendsto (fun ς => ∫ θ in a..b, F ς θ) (𝓝[T] 0) (𝓝 (∫ θ in a..b, f θ)) := by
  -- Mathlib's `Set.uIoc a b` is `Set.Ioc a b` here, and `Set.Ioo a b` differs
  -- from it by the null set `{b}`.
  have huIoc : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  have hne : ∀ᵐ θ : ℝ, θ ≠ b := by
    have : ∀ᵐ θ : ℝ, θ ∉ ({b} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton b)
    simpa using this
  have hshrink : ∀ θ : ℝ, θ ≠ b → θ ∈ Set.uIoc a b → θ ∈ Set.Ioo a b := by
    intro θ hθb hθ
    rw [huIoc] at hθ
    exact ⟨hθ.1, lt_of_le_of_ne hθ.2 hθb⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => C) (eventually_of_mem self_mem_nhdsWithin fun ς hς => huIoc ▸ hmeas ς hς)
    (eventually_of_mem self_mem_nhdsWithin fun ς hς => ?_) intervalIntegrable_const ?_
  · filter_upwards [hbound ς hς, hne] with θ hθ hθb hmem
    simpa [Real.norm_eq_abs] using hθ (hshrink θ hθb hmem)
  · filter_upwards [hlim, hne] with θ hθ hθb hmem
    exact hθ (hshrink θ hθb hmem)

end Lyons
