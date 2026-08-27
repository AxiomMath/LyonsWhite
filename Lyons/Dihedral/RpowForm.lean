/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Spectrum
import Lyons.Dihedral.BlockPowers

/-!
# Fractional powers of a two-by-two dihedral block

The block

`M = ![![U, ζw], ![conj ζ w, U]]`  with `U ≥ w ≥ 0` and `|ζ| = 1`

satisfies `M = U • 1 + w • S` where `S = ![![0, ζ], ![conj ζ, 0]]` is a
self-adjoint involution. Hence `(M - μ₊)(M - μ₋) = w²(S² - 1) = 0`, so by
`Lyons.spectrum_subset_pair_of_mul_eq_zero` the spectrum lies in `{μ₊, μ₋}` — no
characteristic polynomial or eigenvector computation.

On a two-point set `t ↦ t ^ θ` agrees with its linear interpolant, and `cfc` of a
linear function is computed by `cfc_add`, `cfc_const` and `cfc_const_mul_id`.
-/

open Matrix
open scoped ComplexConjugate

namespace Lyons

/-- The involution part of a dihedral block. -/
noncomputable def blockS (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, ζ; conj ζ, 0]

/-- A dihedral block. -/
noncomputable def blockM (U w : ℝ) (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(U : ℂ), ζ * w; conj ζ * w, (U : ℂ)]

/-- `S` is an involution when `ζ` is a unit. -/
theorem blockS_sq {ζ : ℂ} (hζ : ‖ζ‖ = 1) : blockS ζ * blockS ζ = 1 := by
  have hcz : conj ζ * ζ = 1 := by
    rw [mul_comm, Complex.mul_conj']
    norm_cast
    rw [hζ]; norm_num
  have hcz' : ζ * conj ζ = 1 := by rw [mul_comm]; exact hcz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockS, Matrix.mul_apply, Fin.sum_univ_two, hcz, hcz']

/-- The block decomposes as `U • 1 + w • S`. -/
theorem blockM_eq (U w : ℝ) (ζ : ℂ) :
    blockM U w ζ = (U : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (w : ℂ) • blockS ζ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockM, blockS] <;> ring

-- The closing `simp` reduces a `smul`-of-matrix identity to a disjunction whose
-- second branch is `abel`-trivial; pinning it to `simp only` would mean listing
-- the `smul`/`sub` normalisation lemmas, so the style check is disabled here.
set_option linter.flexible false in
/-- The annihilating product: `(M - μ₊)(M - μ₋) = 0`. -/
theorem blockM_annihilating {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (blockM U w ζ - algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (U + w)) *
      (blockM U w ζ - algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (U - w)) = 0 := by
  have hS := blockS_sq hζ
  have halg : ∀ r : ℝ, algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) r
      = (r : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro r
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  rw [blockM_eq, halg, halg]
  have e1 : (U : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (w : ℂ) • blockS ζ
      - ((U + w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (w : ℂ) • (blockS ζ - 1) := by
    push_cast
    module
  have e2 : (U : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (w : ℂ) • blockS ζ
      - ((U - w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (w : ℂ) • (blockS ζ + 1) := by
    push_cast
    module
  rw [e1, e2, smul_mul_smul_comm, sub_mul, mul_add, mul_add, hS]
  simp
  exact Or.inr (by abel)

/-- The spectrum of a dihedral block lies in `{U + w, U - w}`. -/
theorem blockM_spectrum {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    spectrum ℝ (blockM U w ζ) ⊆ {U + w, U - w} :=
  spectrum_subset_pair_of_mul_eq_zero _ _ _ (blockM_annihilating hζ)

/-! ### The functional calculus on a two-point spectrum -/

/-- A dihedral block is self-adjoint. -/
theorem blockM_isSelfAdjoint (U w : ℝ) (ζ : ℂ) :
    IsSelfAdjoint (blockM U w ζ) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockM, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- **`cfc` of a linear function.** On any self-adjoint element,
`cfc (fun t => c₀ + c₁ * t) a = c₀ • 1 + c₁ • a`. -/
theorem cfc_linear (c₀ c₁ : ℝ) {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]
    [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a : A) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => c₀ + c₁ * t) a
      = algebraMap ℝ A c₀ + c₁ • a := by
  rw [cfc_add (a := a) (fun _ : ℝ => c₀) (fun t : ℝ => c₁ * t), cfc_const c₀ a,
    cfc_const_mul_id c₁ a]

/-- **The `θ`-th power of a dihedral block.**

The spectrum has at most two points, so `t ↦ t ^ θ` agrees there with its linear
interpolant, and `cfc` of that is computed by `cfc_linear`. Matching coefficients
against `α • 1 + β • S` gives the claim.

Note that `w ≤ U` is **not** needed: the interpolation argument never uses it,
the two eigenvalues `U ± w` may be arbitrary reals, and only `w ≠ 0` matters (so
that the interpolant is well defined). Positivity of the eigenvalues is what
makes `α, β` nonnegative, which is `Lyons.bp_nonneg`, so the hypothesis belongs
there, not here.

The degenerate case `w = 0` **is** admitted, at the cost of one extra case:
there the block is the scalar `U`, its spectrum is `{U}`, and `bpBeta U 0 θ = 0`
makes the stated formula read `U ^ θ • 1`. Admitting it here is what lets
`Lyons.rhoAlg_sandwich` be stated with no hypothesis on `Vblock a k` — the
alternative pushes a case split through everything downstream of it. -/
@[lyons_tag "lem_block_rpow_form"]
theorem blockM_cfc_rpow {U w θ : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 ≤ w) :
    cfc (fun t : ℝ => t ^ θ) (blockM U w ζ)
      = (bpAlpha U w θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (bpBeta U w θ : ℂ) • blockS ζ := by
  rcases eq_or_lt_of_le hw with rfl | hw
  · -- `w = 0`: a scalar block, whose spectrum is the single point `U`.
    have hsa := blockM_isSelfAdjoint U 0 ζ
    have hconst : (spectrum ℝ (blockM U 0 ζ)).EqOn (fun t : ℝ => t ^ θ)
        (fun _ : ℝ => U ^ θ) := by
      intro t ht
      have htU : t = U := by
        rcases blockM_spectrum hζ ht with h | h <;> simpa using h
      simp [htU]
    rw [cfc_congr hconst, cfc_const _ _ hsa]
    unfold bpAlpha bpBeta
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockS, Algebra.algebraMap_eq_smul_one]
  have hsa := blockM_isSelfAdjoint U w ζ
  set c₁ : ℝ := bpBeta U w θ / w with hc₁
  set c₀ : ℝ := bpAlpha U w θ - bpBeta U w θ * U / w with hc₀
  -- On the two-point spectrum, `t ^ θ` agrees with `c₀ + c₁ t`.
  have hEqOn : (spectrum ℝ (blockM U w ζ)).EqOn (fun t : ℝ => t ^ θ)
      (fun t : ℝ => c₀ + c₁ * t) := by
    intro t ht
    rcases blockM_spectrum hζ ht with h | h
    · subst h
      rw [hc₀, hc₁]
      unfold bpAlpha bpBeta
      field_simp
      ring
    · subst h
      rw [hc₀, hc₁]
      unfold bpAlpha bpBeta
      field_simp
      ring
  rw [cfc_congr hEqOn, cfc_linear c₀ c₁ _ hsa]
  have hwne : (w : ℝ) ≠ 0 := hw.ne'
  have hwneC : ((w : ℝ) : ℂ) ≠ 0 := by simpa using hw.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockM, blockS, Algebra.algebraMap_eq_smul_one, hc₀, hc₁, bpAlpha,
      bpBeta] <;>
    try field_simp <;> try ring

end Lyons
