/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Positive
import Lyons.Converse.Regularised
import Lyons.InversionExtension.Sandwich

/-!
# The reflection sandwich at the test element, and the regularised blocks

The mechanism of the whole counterexample, in one identity:

  `S_{ξ_{n,K,ε},θ,τ} = ξ_{n,K,0}`.

The perturbation `ε` survives in the coefficients of `ξ_{n,K,ε}` but **not** in
those of its sandwich, because the sandwich annihilates the element at exactly
the two blocks that carry `ε` — the ones at `χ_{±K}`.

## Why the two `ε`-blocks die

By `Lyons.Converse.rhoAlg_testElement` the block of `ξ_{n,K,ε}` at `χ_k` is
`!![U, ζw; conj (ζw), U]` with

* `U = w = 1`, `ζ = 1` at `k = ±1`;
* `U = w = ε`, `ζ = ±i` at `k = ±K`;
* `U = w = 0` at every other `k`.

So *every* block of the test element is degenerate in the sense that `U = w`:
the eigenvalue `μ₋ = U - w` is `0`. For `0 < θ < 1` that makes `0 ^ θ = 0`, hence
`α = β` and `γ = δ` in `Lyons.bpAlpha`–`Lyons.bpDelta`, and the diagonal relation
`Lyons.bp_rel_diag` then pins all four products `αγ`, `βδ`, `αδ`, `βγ` to `U/2`.
Feeding that into `Lyons.InvExtBlock.rhoAlg_sandwich` collapses the sandwich's
block to

  `(U/2) · !![ζ + conj ζ, 1 + ζ²; 1 + (conj ζ)², ζ + conj ζ]`,

which depends on `ζ` alone up to the scalar. At `ζ = 1` it is `U · !![1,1;1,1]`,
and at `ζ = ±i` it is **zero**, since `i + conj i = 0` and `1 + i² = 0`. That is
the punchline: the sandwich sees the `±K` blocks through the quarter-turn phase
`ζ = ±i`, which cancels them.

The surviving blocks — `!![1,1;1,1]` at `k = ±1` and `0` elsewhere — are the
blocks of `ξ_{n,K,0}`, so `Lyons.InvExtBlock.rhoAlg_injective` identifies the
sandwich with `ξ_{n,K,0}`.

## The blocks of the regularised element

The blocks of the regularised element share these ingredients and are computed
here too. Adding
`ς(1 - π_G)` shifts every block by `ς(I - ρ_{χ_k,1}(π_G))`, and the block of the
uniform element is the character sum `(2n)⁻¹ ∑_a χ_k(a)` in every entry: `½` in
each entry at `k = 0` and `0` otherwise. So off the trivial character the
regularised block is the old block plus `ς I`, and at the trivial character —
where the test element's own block already vanishes — it is
`(ς/2) !![1,-1;-1,1]`.

## Main results

* `Lyons.Converse.sandwich_testElement` : the sandwich identity
  `S_{ξ_{n,K,ε},θ,τ} = ξ_{n,K,0}`.
* `Lyons.Converse.rhoAlg_regTestElement` : the blocks of the regularised element.

## Implementation notes

The conventions are those of the test-element files: the cyclic group `C` of
order `n` with generator `c` is the additively written `ZMod n` with `c = 1`, so
`z = 1` and `d = 1` become `z = 0` and `d = 0`. The group is
`Lyons.InvExt (ZMod n) 0`, the reflection `τ` is `Lyons.InvExt.b`, which is
`InvExt.refl 0`, and `ρ_{χ_k,1}` is
`InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) 0`.

*`K ≥ 2` suffices.* The hypotheses on `K` and `n` are exactly those of
`Lyons.Converse.rhoAlg_testElement`; nothing here needs more.

*`0 < θ < 1` is used, both ends strictly.* This is not decoration: at `θ = 0` the
sandwich is `τ ξ` and its
block at `χ_K` is `-iε ≠ 0`, so the identity genuinely fails. Strictness is what
gives `0 ^ θ = 0` and `0 ^ (1-θ) = 0`, hence `α = β` and `γ = δ`.
-/

namespace Lyons.Converse

open Matrix
open scoped ComplexConjugate

/-! ### A degenerate block sandwiches to a phase matrix

Both facts in this section are statements about an arbitrary inversion extension,
not about the test element; they are private because the only family they are
applied to is the degenerate one, `U = w`, which is a peculiarity of the test
element. -/

section Degenerate

/-- **The four eigenvalue-power products at a degenerate block.** When `U = w`
the small eigenvalue `U - w` is `0`, so for `0 < θ < 1` the four block powers
`Lyons.bpAlpha`–`Lyons.bpDelta` satisfy `α = β` and `γ = δ`; the diagonal
relation `Lyons.bp_rel_diag` then forces each of the four products to be `t/2`.

Concretely `μ₊ = 2t` and `μ₋ = 0`, hence `α = β = (2t)^θ/2` and
`γ = δ = (2t)^{1-θ}/2`, and all four products equal `t/2`. The computation runs
through the two relations rather than through the explicit powers, so that no
`rpow` arithmetic is needed. -/
private theorem bp_products_of_degenerate {t θ : ℝ} (ht : 0 ≤ t) (hθ : 0 < θ)
    (hθ' : θ < 1) :
    bpAlpha t t θ * bpGamma t t θ = t / 2 ∧ bpBeta t t θ * bpDelta t t θ = t / 2 ∧
      bpAlpha t t θ * bpDelta t t θ = t / 2 ∧ bpBeta t t θ * bpGamma t t θ = t / 2 := by
  have hz1 : (t - t : ℝ) ^ θ = 0 := by rw [sub_self, Real.zero_rpow hθ.ne']
  have hz2 : (t - t : ℝ) ^ (1 - θ) = 0 := by
    rw [sub_self, Real.zero_rpow (by linarith : (1 : ℝ) - θ ≠ 0)]
  have hab : bpAlpha t t θ = bpBeta t t θ := by unfold bpAlpha bpBeta; rw [hz1]; ring
  have hgd : bpGamma t t θ = bpDelta t t θ := by unfold bpGamma bpDelta; rw [hz2]; ring
  have hdiag : bpAlpha t t θ * bpGamma t t θ + bpBeta t t θ * bpDelta t t θ = t :=
    bp_rel_diag ht le_rfl
  have hswap : bpBeta t t θ * bpDelta t t θ = bpAlpha t t θ * bpGamma t t θ := by
    rw [hab, hgd]
  have key : bpAlpha t t θ * bpGamma t t θ = t / 2 := by linarith
  refine ⟨key, by linarith, ?_, ?_⟩
  · rw [← hgd]; exact key
  · rw [← hab]; exact key

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {z : A}
  [Fact (z + z = 0)]

/-- **The sandwich of a degenerate block is a phase matrix.** If
`ρ_{χ,d}(x) = !![t, ζt; conj (ζt), t]` — the shape every block of the test
element has — then for `0 < θ < 1`

  `ρ_{χ,d}(S_{x,θ,ι(d)τ}) = (t/2) · !![ζ + conj ζ, 1 + ζ²; 1 + (conj ζ)², ζ + conj ζ]`.

All four eigenvalue-power products in `Lyons.InvExtBlock.rhoAlg_sandwich` are the
single number `t/2` by `bp_products_of_degenerate`, so the block depends on the
phase `ζ` alone. -/
private theorem rhoAlg_sandwich_degenerate (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hpos : IsPos x) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 1) (hχ : χ z = 1) {t : ℝ} (ht : 0 ≤ t) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hU : ((t : ℝ) : ℂ) = InvExtBlock.Ublock x χ)
    (hV : InvExtBlock.Vblock x d χ = ζ * ((t : ℝ) : ℂ)) :
    InvExtBlock.rhoAlg χ d (sandwich x (InvExt.refl d) θ)
      = ((t / 2 : ℝ) : ℂ) •
          !![ζ + conj ζ, 1 + ζ ^ 2; 1 + (conj ζ) ^ 2, ζ + conj ζ] := by
  obtain ⟨hαγ, hβδ, hαδ, hβγ⟩ := bp_products_of_degenerate ht hθ hθ'
  rw [InvExtBlock.rhoAlg_sandwich χ d x hpos hθ.le hθ'.le hχ hζ ht hU hV,
    hαγ, hβδ, hαδ, hβγ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end Degenerate

/-! ### The blocks of the sandwich at the test element -/

variable {n : ℕ} [NeZero n]

/-- The two transforms of the test element read off its block, and the block of
its sandwich computed from them.

Packaging the four cases of `Lyons.Converse.rhoAlg_testElement` into a single
hypothesis `hb` in the degenerate shape `!![t, ζt; conj (ζt), t]` is what keeps
the case analysis below to one line per case: the caller supplies `t` and `ζ`,
and the phase matrix comes back. -/
private theorem rhoAlg_sandwich_testElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    {ε : ℝ} (hε : 0 ≤ ε) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (k : ZMod n) {t : ℝ}
    (ht : 0 ≤ t) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hb : InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
        (0 : ZMod n) (testElement n K ε)
      = !![((t : ℝ) : ℂ), ζ * ((t : ℝ) : ℂ);
           conj (ζ * ((t : ℝ) : ℂ)), ((t : ℝ) : ℂ)]) :
    InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n)
        (sandwich (testElement n K ε) (InvExt.refl (0 : ZMod n)) θ)
      = ((t / 2 : ℝ) : ℂ) •
          !![ζ + conj ζ, 1 + ζ ^ 2; 1 + (conj ζ) ^ 2, ζ + conj ζ] := by
  have hχ0 : (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n) = 1 :=
    AddChar.map_zero_eq_one _
  have hU : ((t : ℝ) : ℂ) = InvExtBlock.Ublock (testElement n K ε)
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) := by
    rw [InvExtBlock.Ublock_eq_entry _ (0 : ZMod n), hb]
    simp
  have hV : InvExtBlock.Vblock (testElement n K ε) (0 : ZMod n)
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) = ζ * ((t : ℝ) : ℂ) := by
    have h := InvExtBlock.char_mul_Vblock_eq_entry
      (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n) (testElement n K ε)
    rw [hb, hχ0, one_mul] at h
    rw [h]
    simp
  exact rhoAlg_sandwich_degenerate _ _ _ (isPos_testElement hK hn hε) hθ hθ' hχ0 ht
    hζ hU hV

/-! ### The sandwich identity -/

/-- **The reflection sandwich at the test element.**

  `S_{ξ_{n,K,ε},θ,τ} = ξ_{n,K,0}`.

This is the mechanism of the counterexample. The perturbation `ε` enters
`ξ_{n,K,ε}` only through its blocks at `χ_{±K}`, whose phase is `ζ = ±i`; and
`rhoAlg_sandwich_degenerate` shows the sandwich's block is `(U/2)` times a matrix
built from `ζ + conj ζ` and `1 + ζ^{±2}`, both of which vanish at `ζ = ±i`. So
the sandwich kills exactly the two blocks that carry `ε`, and what is left is the
block data of `ξ_{n,K,0}`.

`Lyons.InvExtBlock.rhoAlg_injective` at `d = 0` reduces the identity to that
comparison of blocks, and `Lyons.Converse.cyclicAddChar_bijective` makes every
character a `χ_k`.

**Where the hypotheses are used.** `hK` and `hn` enter only through
`Lyons.Converse.rhoAlg_testElement`, which needs the four residues `1`, `-1`,
`K`, `-K` of `ℤ/n` pairwise distinct; `hε` only through
`Lyons.Converse.isPos_testElement`, since the sandwich is defined at positive
elements; `hθ` and `hθ'` are `θ ∈ (0,1)`, both ends needed — see the module notes.

The reflection `τ` is `Lyons.InvExt.b`, which in this model is
`InvExt.refl 0`, so the sandwich is taken at the outside index
`d = 0` that `Lyons.Converse.testElement`'s coefficients are written at. -/
@[lyons_tag "lem_x_eps_sandwich"]
theorem sandwich_testElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) {ε : ℝ}
    (hε : 0 ≤ ε) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) :
    sandwich (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) θ
      = testElement n K 0 := by
  have hτ : (InvExt.b : InvExt (ZMod n) 0) = InvExt.refl 0 := rfl
  rw [hτ]
  refine InvExtBlock.rhoAlg_injective (0 : ZMod n) fun χ ↦ ?_
  obtain ⟨k, rfl⟩ :=
    (cyclicAddChar_bijective (ZMod.card n) (exists_zsmul_one (n := n))).surjective χ
  rw [rhoAlg_testElement hK hn 0 k]
  -- `k = ±1`: the phase is `1`, and the block survives as `!![1,1;1,1]`.
  by_cases h1 : k = 1 ∨ k = -1
  · have hb : InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
        (0 : ZMod n) (testElement n K ε)
        = !![((1 : ℝ) : ℂ), (1 : ℂ) * ((1 : ℝ) : ℂ);
             conj ((1 : ℂ) * ((1 : ℝ) : ℂ)), ((1 : ℝ) : ℂ)] := by
      rw [rhoAlg_testElement hK hn ε k, if_pos h1]
      norm_num
    rw [rhoAlg_sandwich_testElement hK hn hε hθ hθ' k zero_le_one (by norm_num) hb,
      if_pos h1]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  rw [if_neg h1]
  -- `k = K`: the phase is `i`, and the block dies.
  by_cases hK' : k = (K : ZMod n)
  · have hb : InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
        (0 : ZMod n) (testElement n K ε)
        = !![((ε : ℝ) : ℂ), Complex.I * ((ε : ℝ) : ℂ);
             conj (Complex.I * ((ε : ℝ) : ℂ)), ((ε : ℝ) : ℂ)] := by
      rw [rhoAlg_testElement hK hn ε k, if_neg h1, if_pos hK']
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring
    rw [rhoAlg_sandwich_testElement hK hn hε hθ hθ' k hε (by simp) hb, if_pos hK']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.conj_I, Complex.I_sq]
  rw [if_neg hK']
  -- `k = -K`: the phase is `-i`, and the block dies for the same reason.
  by_cases hmK : k = -(K : ZMod n)
  · have hb : InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
        (0 : ZMod n) (testElement n K ε)
        = !![((ε : ℝ) : ℂ), (-Complex.I) * ((ε : ℝ) : ℂ);
             conj ((-Complex.I) * ((ε : ℝ) : ℂ)), ((ε : ℝ) : ℂ)] := by
      rw [rhoAlg_testElement hK hn ε k, if_neg h1, if_neg hK', if_pos hmK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring
    rw [rhoAlg_sandwich_testElement hK hn hε hθ hθ' k hε (by simp) hb, if_pos hmK]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.conj_I, Complex.I_sq]
  rw [if_neg hmK]
  -- Every other `k`: the block of the test element already vanishes.
  have hb : InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
      (0 : ZMod n) (testElement n K ε)
      = !![((0 : ℝ) : ℂ), (1 : ℂ) * ((0 : ℝ) : ℂ);
           conj ((1 : ℂ) * ((0 : ℝ) : ℂ)), ((0 : ℝ) : ℂ)] := by
    rw [rhoAlg_testElement hK hn ε k, if_neg h1, if_neg hK', if_neg hmK]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [rhoAlg_sandwich_testElement hK hn hε hθ hθ' k le_rfl (by norm_num) hb]
  simp

/-! ### The blocks of the regularised element

`ρ_{χ_k,1}` is an `ℝ`-algebra homomorphism, so the only new computation the
regularised element needs is the block of the uniform element `π_G`. -/

/-- **The character sum of `χ_k`.** `∑_{a ∈ ℤ/n} χ_k(a)` is `n` at `k = 0` and
`0` otherwise.

This is `Lyons.Converse.sum_omegaN_pow` read through the defining prescription
`χ_k(c^j) = ω_n^{kj}` of `Lyons.Converse.cyclicChar`, at the standard model where
`c = 1` and `c^j` is the residue `j` itself. -/
private theorem sum_cyclicAddChar (k : ZMod n) :
    ∑ a : ZMod n, cyclicAddChar (ZMod.card n) exists_zsmul_one k a
      = if k = 0 then (n : ℂ) else 0 := by
  rw [← sum_omegaN_pow n k]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j.val : ℕ) • (1 : ZMod n) = j := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  calc cyclicAddChar (ZMod.card n) exists_zsmul_one k j
      = cyclicChar (ZMod.card n) (exists_zsmul_one (n := n)) k j :=
        congrFun (cyclicAddChar_coe k) j
    _ = cyclicChar (ZMod.card n) (exists_zsmul_one (n := n)) k
          ((j.val : ℕ) • (1 : ZMod n)) := by rw [hj]
    _ = omegaN n ^ (k * j).val := cyclicChar_apply_index k j

/-- The transform of a constant coefficient family, from `sum_cyclicAddChar`.
Both coefficient families of `π_G` are constant, so this is the only shape of
transform the uniform element produces. -/
private theorem dft_const (c : ℂ) (k : ZMod n) :
    AddCharFourier.dft (fun _ : ZMod n => c)
        (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
      = c * if k = 0 then (n : ℂ) else 0 := by
  rw [AddCharFourier.dft_apply, ← Finset.mul_sum, sum_cyclicAddChar]

/-- Every coefficient of `π_G` is `(2n)⁻¹`: the group `G_{ℤ/n,0}` has `2n`
elements by `Lyons.InvExt.card`, the underlying set of `G` being `C × ℤ/2`. -/
private theorem co_uniform_invExt (g : InvExt (ZMod n) 0) :
    co (uniform (InvExt (ZMod n) 0)) g = (2 * (n : ℝ))⁻¹ := by
  rw [coe_uniform, InvExt.card, ZMod.card]
  push_cast
  ring

/-- **The block of the uniform element.** `ρ_{χ_k,1}(π_G)` is `½ !![1,1;1,1]` at
`k = 0` and `0` otherwise.

Both transforms are `(2n)⁻¹ ∑_a χ_k(a)`, hence `½` at `k = 0` and `0` otherwise;
`Lyons.InvExtBlock.rhoAlg_entries` assembles the matrix, its `χ_k(z)` being `1`
because `z = 0`. -/
private theorem rhoAlg_uniform (k : ZMod n) :
    InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n)
        (uniform (InvExt (ZMod n) 0))
      = if k = 0 then (2 : ℂ)⁻¹ • !![1, 1; 1, 1] else 0 := by
  have hne : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hu : InvExtBlock.uCoeff (uniform (InvExt (ZMod n) 0))
      = fun _ : ZMod n => (2 * (n : ℂ))⁻¹ := by
    funext a
    simp only [InvExtBlock.uCoeff, co_uniform_invExt]
    push_cast
    ring
  have hv : InvExtBlock.vCoeff (uniform (InvExt (ZMod n) 0)) 0
      = fun _ : ZMod n => (2 * (n : ℂ))⁻¹ := by
    funext a
    simp only [InvExtBlock.vCoeff, co_uniform_invExt]
    push_cast
    ring
  have key : ∀ f : ZMod n → ℂ, f = (fun _ : ZMod n => (2 * (n : ℂ))⁻¹) →
      AddCharFourier.dft f (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
        = if k = 0 then (2 : ℂ)⁻¹ else 0 := by
    intro f hf
    rw [hf, dft_const]
    split_ifs
    · field_simp
    · rw [mul_zero]
  have hχ0 : (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n) = 1 :=
    AddChar.map_zero_eq_one _
  rw [InvExtBlock.rhoAlg_entries, InvExtBlock.Ublock, InvExtBlock.Vblock,
    key _ hu, key _ hv, hχ0, one_mul]
  split_ifs <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [map_ofNat]

/-- **The blocks of the regularised element.**

  `ρ_{χ_k,1}(ξ_{n,K,ε,ς}) = ρ_{χ_k,1}(ξ_{n,K,ε}) + ς I` for `k ≠ 0`, and
  `ρ_{χ_0,1}(ξ_{n,K,ε,ς}) = (ς/2) !![1,-1;-1,1]`.

`Lyons.InvExtBlock.rhoAlg` is a unital `ℝ`-algebra homomorphism, so the
definition of `Lyons.Converse.regTestElement` gives
`ρ(ξ_{n,K,ε,ς}) = ρ(ξ_{n,K,ε}) + ς(I - ρ(π_G))`, and `rhoAlg_uniform` evaluates
the last block. At `k = 0` the test element contributes nothing, by
`Lyons.Converse.rhoAlg_testElement` — the "otherwise" case, since `0` is none of
`1`, `-1`, `K`, `-K` — and `I - ½!![1,1;1,1]` is `½!![1,-1;-1,1]`.

The two cases are written as one `if` on `k = 0`, with the `k = 0` value first.
Here `I` is `(1 : Matrix (Fin 2) (Fin 2) ℂ)` and `ς I` is the real scalar action
`ς • 1`, the shape `Lyons.InvExtBlock.rhoAlg` transports by `map_smul`.

**Where the hypotheses are used.** `hK` and `hn` are needed only in the `k = 0`
branch, and only to put `0` outside `{1, -1, K, -K}`: it is enough that `1` and
`K` are nonzero residues of `ℤ/n`, and each is an integer strictly between `0`
and `n` precisely because `2 ≤ K` and `2K < n`. These are exactly the hypotheses
`Lyons.Converse.rhoAlg_testElement` asks for. No sign condition on `ε` or `ς` is
needed. -/
@[lyons_tag "lem_x_eps_reg_block"]
theorem rhoAlg_regTestElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε ς : ℝ)
    (k : ZMod n) :
    InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) (0 : ZMod n)
        (regTestElement n K ε ς)
      = if k = 0 then (ς / 2 : ℝ) • !![1, -1; -1, 1]
        else InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k)
            (0 : ZMod n) (testElement n K ε) + ς • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [regTestElement, map_add, map_smul, map_sub, map_one, rhoAlg_uniform]
  split_ifs with hk
  · -- `k = 0`: the block of the test element vanishes as well.
    subst hk
    have hcast : ∀ m : ℤ, 0 < m → m < (n : ℤ) → ((m : ZMod n)) ≠ 0 := by
      intro m h0 hm
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact fun hdvd => absurd (Int.le_of_dvd h0 hdvd) (by omega)
    have c1 : (1 : ZMod n) ≠ 0 := by
      have h := hcast 1 (by norm_num) (by omega)
      push_cast at h
      exact h
    have cK : ((K : ZMod n)) ≠ 0 := hcast K (by omega) (by omega)
    rw [rhoAlg_testElement hK hn ε 0,
      if_neg (by rintro (h | h); exacts [c1 h.symm, c1 (by linear_combination h)]),
      if_neg fun h => cK h.symm, if_neg fun h => cK (by linear_combination h)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring
  · rw [sub_zero]

end Lyons.Converse
