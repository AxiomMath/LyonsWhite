/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Lyons.GroupAlgebra.Sqrt
import Lyons.Walk.Basic

/-!
# Positivity in the group algebra: scalars, squares, and three ambient inputs

Constructing the counterexample to rate-monotonicity needs a handful of closure
properties of `Lyons.IsPos` that the earlier files never had to state, together
with the ambient facts they rest on. All of it is elementary; the point of
collecting it here is that each piece is used more than once downstream.

## What is not about the group algebra, and why

Three of the entries below are about matrices, or about a Banach algebra, rather
than about `MonoidAlgebra`:

* `Lyons.posSemidef_iff_exists_conjTranspose_mul_self` is the factorisation
  `M = Nᴴ * N`. Mathlib has the easy half,
  `Matrix.posSemidef_conjTranspose_mul_self`; the converse is the positive square
  root, which this development already owns as `Lyons.msqrt`.
* `Lyons.mpow_smul` is homogeneity of the fractional power in the scalar.
  Nothing in Mathlib's `CFC.rpow` API has the shape
  `(κ • a) ^ θ = κ ^ θ • a ^ θ`, so it is proved here from the composition rule
  `cfc_comp_const_mul` together with `Real.mul_rpow`.
* `Lyons.exp_smul_of_isIdempotentElem` is `e^{sQ} = 1 + (e^s - 1) Q` for an
  idempotent `Q`, proved from the exponential series.

## The exponential is stated in a Banach algebra, not in `Matrix`

The natural home of `exp_smul_of_isIdempotentElem` would be a complex square
matrix, but the proof uses nothing beyond a complete normed `ℝ`-algebra, so that
is where it is stated. The generalisation is not gratuitous: `NormedSpace.exp` is
defined by a `tsum` and therefore depends on the `TopologicalSpace` instance, and
`Matrix n n ℂ` carries two — the ambient product topology and the one under the
`Norms.Operator`-scoped operator norm that the series lemmas force. At `Matrix`
the statement and its proof land on opposite sides of that diamond and do not
even `rw` against each other. In an abstract `[NormedRing 𝔸]` there is one
topology and the question does not arise; the matrix instance is then recovered
at the use site, which has to open the scoped norm anyway.

## Main definitions

* `Lyons.IsPosDefOffConst` : positive definiteness off the constants.

## Main results

* `Lyons.posSemidef_iff_exists_conjTranspose_mul_self` : `M ⪰ 0` exactly when
  `M = Nᴴ * N`.
* `Lyons.mpow_smul` : the matrix fractional power is homogeneous in the scalar.
* `Lyons.IsPos.smul` : positivity is preserved by nonnegative scalars.
* `Lyons.isPos_invol_mul_self` : every element `y⋆ y` is positive.
* `Lyons.powElt_smul` : the group-algebra fractional power is homogeneous in the
  scalar.
* `Lyons.exp_smul_of_isIdempotentElem` : `e^{sQ} = 1 + (e^s - 1) Q` for an
  idempotent `Q`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

/-! ### Matrix inputs

`Lyons.msqrt` and `Lyons.mpow` are stated in `Lyons.GroupAlgebra.Sqrt` at an
index type carrying a group structure, but neither uses it — the continuous
functional calculus on `Matrix n n ℂ` needs only `Fintype` and `DecidableEq` —
so both are available here at a bare index type, which is the generality these
two matrix facts deserve. -/

section Matrices

variable {n : Type*} [Fintype n]

/-- **A matrix is positive semidefinite exactly when it is a square `Nᴴ * N`.**

Only `←` is in Mathlib, as `Matrix.posSemidef_conjTranspose_mul_self`; `→` is the
positive square root `Lyons.msqrt`, which is Hermitian and squares to `M`. The
`DecidableEq n` that the functional calculus needs is used only inside the proof,
so it is supplied by `classical` rather than assumed. -/
@[lyons_tag "lem_ext_pos_sq"]
theorem posSemidef_iff_exists_conjTranspose_mul_self {M : Matrix n n ℂ} :
    M.PosSemidef ↔ ∃ N : Matrix n n ℂ, M = Nᴴ * N := by
  classical
  refine ⟨fun hM => ⟨msqrt M, ?_⟩, fun ⟨N, hN⟩ => hN ▸ posSemidef_conjTranspose_mul_self N⟩
  have hle : (0 : Matrix n n ℂ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  rw [(Matrix.nonneg_iff_posSemidef.mp (msqrt_nonneg M hle)).isHermitian,
    msqrt_mul_self hle]

variable [DecidableEq n]

/-- **Fractional powers of a matrix are homogeneous in the scalar.**

`cfc_comp_const_mul` turns the calculus of `κ • M` into the calculus of the
rescaled function `t ↦ (κ * t) ^ θ` at `M`, and `Real.mul_rpow` splits that as
`κ ^ θ * t ^ θ` on the spectrum, which is nonnegative because `M` is.

Positivity of `M` is written `0 ≤ M` in the scoped Loewner order, as everywhere
in `Lyons.GroupAlgebra.Sqrt`; `Matrix.nonneg_iff_posSemidef` converts. Only
`0 ≤ κ` and `0 ≤ θ` are used — the latter for continuity of `t ↦ t ^ θ` — but the
strict hypotheses are kept, since `Lyons.powElt_smul` below needs them anyway. -/
@[lyons_tag "lem_ext_rpow_smul"]
theorem mpow_smul {M : Matrix n n ℂ} (hM : (0 : Matrix n n ℂ) ≤ M) {κ θ : ℝ}
    (hκ : 0 < κ) (hθ : 0 < θ) : mpow (κ • M) θ = (κ ^ θ) • mpow M θ := by
  have hsa : IsSelfAdjoint M := (Matrix.nonneg_iff_posSemidef.mp hM).isHermitian
  have hc : Continuous fun t : ℝ => t ^ θ := Real.continuous_rpow_const hθ.le
  rw [mpow, mpow, ← cfc_comp_const_mul κ (fun t : ℝ => t ^ θ) M hc.continuousOn hsa,
    cfc_congr (g := fun t : ℝ => κ ^ θ * t ^ θ)
      fun r hr => Real.mul_rpow hκ.le (spectrum_nonneg_of_nonneg hM r hr),
    cfc_const_mul (κ ^ θ) (fun t : ℝ => t ^ θ) M hc.continuousOn]

end Matrices

/-! ### Positivity in the group algebra -/

variable {H : Type*} [Group H] [Fintype H]

/-- **Positivity is preserved by nonnegative scalars.**

The scalar multiple usually written `κ x` is here the `ℝ`-module action `κ • x`
on `MonoidAlgebra ℝ H`, which is the same element. -/
@[lyons_tag "lem_smul_pos"]
protected theorem IsPos.smul {x : MonoidAlgebra ℝ H} (hx : IsPos x) {κ : ℝ}
    (hκ : 0 ≤ κ) : IsPos (κ • x) := by
  rw [IsPos, L_smul]
  exact Matrix.PosSemidef.smul hx hκ

/-- **Every element of the form `y⋆ y` is positive.**

`L` turns the product into `(L y)ᴴ * L y` by `Lyons.L_mul` and `Lyons.L_invol`,
and `Lyons.posSemidef_iff_exists_conjTranspose_mul_self` finishes. -/
@[lyons_tag "lem_star_mul_pos"]
theorem isPos_invol_mul_self (y : MonoidAlgebra ℝ H) : IsPos (invol y * y) := by
  rw [IsPos, L_mul, L_invol]
  exact posSemidef_iff_exists_conjTranspose_mul_self.mpr ⟨L y, rfl⟩

variable [DecidableEq H]

/-- **Fractional powers in the group algebra are homogeneous in the scalar.**

As with `Lyons.IsPos.smul`, `κ x` is written as the module action `κ • x`. -/
@[lyons_tag "lem_rpow_smul"]
theorem powElt_smul {x : MonoidAlgebra ℝ H} (hx : IsPos x) {κ θ : ℝ} (hκ : 0 < κ)
    (hθ : 0 < θ) : powElt (κ • x) θ = (κ ^ θ) • powElt x θ := by
  refine L_injective ?_
  rw [L_powElt _ (hx.smul hκ.le) hθ.le, L_smul, L_smul,
    mpow_smul ((isPos_iff_le x).mp hx) hκ hθ, L_powElt _ hx hθ.le]

/-- **Positive definiteness off the constants.** The quadratic form of `L x` is
strictly positive on every nonzero column vector killed by `L` of the uniform
element.

The quadratic form is written exactly as Mathlib writes it in
`Matrix.posDef_iff_dotProduct_mulVec`, namely `0 < star η ⬝ᵥ (L x *ᵥ η)` in the
scoped order on `ℂ`, which unfolds to `0 < (⬝).re ∧ (⬝).im = 0`. That is the
faithful reading of `⟨L_x η, η⟩ > 0`: the weaker
`0 < (star η ⬝ᵥ (L x *ᵥ η)).re` would drop the assertion that the form is real,
which the inequality presupposes. -/
@[lyons_tag "def_posdef_off_const"]
def IsPosDefOffConst (x : MonoidAlgebra ℝ H) : Prop :=
  ∀ ⦃η : H → ℂ⦄, η ≠ 0 → L (uniform H) *ᵥ η = 0 → 0 < star η ⬝ᵥ (L x *ᵥ η)

/-! ### The exponential of a scalar multiple of an idempotent -/

/-- **The exponential of a real multiple of an idempotent.** Stated at a complete
normed `ℝ`-algebra rather than at matrices; see the module docstring for why the
matrix statement cannot be the primitive one.

Proved from the series: `(s • Q) ^ q = s ^ q • Q` for `q ≥ 1` because `Q` is
idempotent, so the series is `1` plus `Real.exp s - 1` times `Q`. The `q = 0`
term is `1` rather than `Q`, and that one discrepancy is carried by the one-point
summand `1 - Q`.

Mathlib's `IsIdempotentElem Q` is `Q ^ 2 = Q`. -/
@[lyons_tag "lem_exp_idempotent"]
theorem exp_smul_of_isIdempotentElem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {Q : 𝔸} (hQ : IsIdempotentElem Q) (s : ℝ) :
    NormedSpace.exp (s • Q) = 1 + (Real.exp s - 1) • Q := by
  -- the scalar exponential series, pushed into `𝔸` along `r ↦ r • Q`
  have hscal : HasSum (fun k : ℕ => ((Nat.factorial k : ℝ)⁻¹ • s ^ k) • Q)
      (Real.exp s • Q) := by
    have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) s).map
      (LinearMap.toSpanSingleton ℝ 𝔸 Q).toAddMonoidHom
      (continuous_id.smul continuous_const)
    simpa [Function.comp_def, Real.exp_eq_exp_ℝ] using h
  -- the `q = 0` correction: the constant term of the series is `1`, not `Q`
  have hcorr : HasSum (fun k : ℕ => if k = 0 then (1 : 𝔸) - Q else 0) (1 - Q) :=
    hasSum_ite_eq 0 _
  have hterm : ∀ k : ℕ, ((Nat.factorial k : ℝ)⁻¹ • (s • Q) ^ k)
      = ((Nat.factorial k : ℝ)⁻¹ • s ^ k) • Q + (if k = 0 then (1 : 𝔸) - Q else 0) := by
    intro k
    cases k with
    | zero => simp
    | succ m => simp [smul_pow, hQ.pow_succ_eq m, smul_smul]
  have hexp := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • Q)).unique
    (by simpa only [hterm] using hscal.add hcorr)
  rw [hexp, sub_smul, one_smul]
  abel

end Lyons
