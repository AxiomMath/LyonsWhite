/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Jp
import Lyons.Dihedral.Sandwich
import Lyons.GroupAlgebra.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The reflection energy

The single real number whose sign decides whether rate-monotonicity holds. For a
positive element `x` of `ℝ[G]` and an element `c ∈ G`, the **reflection
energy** is

  `E_p(x; c) = ∫₀¹ ∑_{g ∈ G} J_p(x_g) · ((S_{x,θ,c})_g - x_g) dθ`,

where `J_p` is the signed power `Lyons.Converse.signedPow` and `S_{x,θ,c}` is
the reflection sandwich `x^θ · c · x^{1-θ}`, `Lyons.sandwich`.

It is the derivative at time zero of the `ℓ^p` distance along the rate
perturbation exhibited away from the even integers, so proving it *positive* at a
well-chosen element is what breaks rate-monotonicity. At an even exponent the
proof of `Lyons.rateMonotonic_dihedral_even` shows the same quantity is `≤ 0` —
the positive and negative results meet here.

## Main definitions

* `Lyons.Converse.energy` : the reflection energy `E_p(x; c)`.

## Implementation notes

The definition carries no hypotheses beyond those needed to *write down* the
integral: `x` need not be positive, `p` need not be `≥ 1`, and `G` is an
arbitrary finite group rather than an inversion extension.

* Positivity of `x` is what makes `x^θ` meaningful, but `Lyons.powElt` — and
  hence `Lyons.sandwich` — is a total function, defined by the functional
  calculus on `L x` whatever `x` is. Positivity is what makes the sandwich
  *equal* `x^θ c x^{1-θ}`, and that is `Lyons.sandwich_eq_mul`'s hypothesis, not
  this definition's.
* `p ≥ 1` never enters: `Lyons.Converse.signedPow` is defined for every real `p`.
* Nothing in the integrand looks at the group's structure.

Carrying unused hypotheses in a definition would force every consumer to supply
them before it could even name the object, so they are dropped. Each is
reintroduced exactly where a *lemma* needs it.

The integrand is only meaningful for `θ ∈ (0, 1)`, since that is the range the
sandwich admits, and the two endpoint values do not affect the integral. The
integrand as written is total in `θ`, so no extension has to be chosen and no
`ContinuousOn` bookkeeping is needed; the interval integral over `(0, 1)` is
taken as written.
-/

open Finset MeasureTheory
open scoped MatrixOrder ComplexOrder

namespace Lyons.Converse

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The **reflection energy** `E_p(x; c)`:

  `∫₀¹ ∑_{g ∈ G} J_p(x_g) · ((S_{x,θ,c})_g - x_g) dθ`.

See the module docstring for the three hypotheses this definition does not carry
(`x ⪰ 0`, `p ≥ 1`, and the group being an inversion extension) — each is needed
by a lemma about the energy, none by the energy itself. -/
@[lyons_tag "def_Ep"]
noncomputable def energy (p : ℝ) (x : MonoidAlgebra ℝ G) (c : G) : ℝ :=
  ∫ θ in (0 : ℝ)..1, ∑ g : G, signedPow p (co x g) * (co (sandwich x c θ) g - co x g)

/-- The energy unfolded, for rewriting. -/
theorem energy_def (p : ℝ) (x : MonoidAlgebra ℝ G) (c : G) :
    energy p x c
      = ∫ θ in (0 : ℝ)..1,
          ∑ g : G, signedPow p (co x g) * (co (sandwich x c θ) g - co x g) := rfl

/-! ### Homogeneity -/

/-- **The sandwich is homogeneous of degree one.** `S_{κx,θ,c} = κ S_{x,θ,c}`.

The two fractional powers contribute `κ^θ` and `κ^{1-θ}`, whose product is
`κ^{θ + (1 - θ)} = κ`. It is separated out from
`Lyons.Converse.energy_smul` because it is a statement about the sandwich and not
about the energy, and because the interval `0 < θ < 1` is needed for it but not
for the energy. -/
theorem sandwich_smul {x : MonoidAlgebra ℝ G} (hx : IsPos x) (c : G) {κ θ : ℝ}
    (hκ : 0 < κ) (hθ : 0 < θ) (hθ' : θ < 1) :
    sandwich (κ • x) c θ = κ • sandwich x c θ := by
  have hθ1 : (0 : ℝ) < 1 - θ := by linarith
  -- `hx.smul` would resolve through the unfolded type to
  -- `Matrix.PosSemidef.smul`; `Lyons.IsPos.smul` is `protected` and must be named.
  rw [sandwich_eq_mul _ (IsPos.smul hx hκ.le) c hθ.le hθ'.le,
    sandwich_eq_mul _ hx c hθ.le hθ'.le, powElt_smul hx hκ hθ,
    powElt_smul hx hκ hθ1, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    smul_smul, ← Real.rpow_add hκ]
  norm_num

/-- **The energy is homogeneous of degree `p`.** `E_p(κx; c) = κ^p E_p(x; c)`.

Two homogeneities multiply: the sandwich difference scales by `κ`
(`Lyons.Converse.sandwich_smul`) and `J_p` scales by `κ^{p-1}`
(`Lyons.Converse.signedPow_const_mul`), and `κ^{p-1} · κ = κ^p`.

The integrands agree only on the **open** interval: `sandwich_smul` needs
`0 < θ < 1`, because at `θ = 1` the exponent `1 - θ` vanishes and the fractional
power is no longer homogeneous. So the two integrals are compared almost
everywhere rather than pointwise — `Set.uIoc 0 1` is `Ioc 0 1`, and it differs
from `Ioo 0 1` by the single point `1`, which `MeasureTheory.Measure.ae_ne`
discards. -/
@[lyons_tag "lem_Ep_homogeneous"]
theorem energy_smul (p : ℝ) {x : MonoidAlgebra ℝ G} (hx : IsPos x) (c : G)
    {κ : ℝ} (hκ : 0 < κ) : energy p (κ • x) c = κ ^ p * energy p x c := by
  rw [energy_def, energy_def, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (1 : ℝ)]
    with θ hθne hθmem
  -- `uIoc 0 1 = Ioc 0 1`, and `θ ≠ 1`, so `0 < θ < 1`.
  rw [Set.uIoc_of_le zero_le_one] at hθmem
  have hθ : 0 < θ := hθmem.1
  have hθ' : θ < 1 := lt_of_le_of_ne hθmem.2 hθne
  -- `κ^{p-1} · κ = κ^p`, the two homogeneities multiplying.
  have hpow : κ ^ (p - 1) * κ = κ ^ p := by
    rw [Real.rpow_sub hκ, Real.rpow_one, div_mul_cancel₀ _ hκ.ne']
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [co_smul, sandwich_smul hx c hκ hθ hθ', co_smul, signedPow_const_mul hκ,
    ← hpow]
  ring

end Lyons.Converse
