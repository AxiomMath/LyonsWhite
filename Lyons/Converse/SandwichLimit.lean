/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Analysis.EventuallyPos
import Lyons.Analysis.Imported
import Lyons.Converse.Energy
import Lyons.Converse.Sandwich
import Lyons.Dihedral.BlockPowersCont

/-!
# The block data of the regularised element, and its dependence on `ς`

The coefficients of the sandwich `𝓢_{x_ς,θ,τ}` converge as `ς → 0⁺` because the
entries of `ρ_{χ_k,1}(𝓢_{x_ς,θ,τ})` do, and by `Lyons.rhoAlg_sandwich` each entry
is a fixed polynomial in the four block powers formed from
`U(ς) = U^{x_ς}(χ_k)` and `w(ς) = ‖V^{x_ς,1}(χ_k)‖`. So the argument splits into
three ingredients:

* the closed forms of `U(ς)` and `w(ς)`, both affine in `ς` (this file);
* continuity of the block powers in `(U, w)`
  (`Lyons.Dihedral.BlockPowersCont`);
* Fourier inversion, to get from block entries back to coefficients
  (`Lyons.Converse.tendsto_co_of_tendsto_blocks`).

## Where the closed form comes from

`Lyons.Converse.rhoAlg_regTestElement` already gives the whole block in closed
form, and it is *affine* in `ς`:

```
k = 0 : (ς/2) • !![1, -1; -1, 1]
k ≠ 0 : ρ_{χ_k,1}(ξ_{n,K,ε}) + ς • 1
```

Reading `U` and `w` off that needs only `Lyons.InvExtBlock.rhoAlg_entries`, which
says the `(0,0)` entry of `ρ` is `U` and the `(1,0)` entry is `conj V`. The
identity matrix contributes `ς` to the `(0,0)` entry and nothing to `(1,0)`, so

  `U(ς) = U(0) + ς`,  `V(ς) = V(0)`   for `k ≠ 0`,
  `U(ς) = ς/2`,       `V(ς) = -ς/2`   for `k = 0`.

## Implementation notes

`C` is `ZMod n` written additively, so `z = 0` and `d = 0`, and `τ` is
`Lyons.InvExt.b`. The hypotheses on `K` and `n` are inherited from
`rhoAlg_regTestElement` as `2 ≤ K` and `2 * K < n`.
-/
open Matrix Complex
open scoped ComplexConjugate

namespace Lyons.Converse

variable {n : ℕ} [NeZero n]

/-- The character `χ_k` of the cyclic group, as this development spells it. A
local abbreviation to keep the statements below readable. -/
private noncomputable abbrev chi (k : ZMod n) : AddChar (ZMod n) ℂ :=
  cyclicAddChar (ZMod.card n) exists_zsmul_one k

/-- **The abelian transform of the regularised element**, explicitly.
`U(ς) = ς/2` at the trivial character and `U(0) + ς` elsewhere.

Read off `Lyons.Converse.rhoAlg_regTestElement` via `rhoAlg_entries`: the
`(0,0)` entry of `ρ` is `U`, and `ς • 1` contributes `ς` there. -/
theorem Ublock_regTestElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    (ε ς : ℝ) (k : ZMod n) :
    InvExtBlock.Ublock (regTestElement n K ε ς) (chi k)
      = if k = 0 then ((ς / 2 : ℝ) : ℂ)
        else InvExtBlock.Ublock (testElement n K ε) (chi k) + (ς : ℂ) := by
  have hrho := rhoAlg_regTestElement (n := n) hK hn ε ς k
  rw [InvExtBlock.rhoAlg_entries] at hrho
  split_ifs at hrho ⊢ with hk
  · -- `k = 0`: the whole block is `(ς/2) • !![1, -1; -1, 1]`.
    have h00 := congrFun (congrFun hrho 0) 0
    simpa using h00
  · -- `k ≠ 0`: the block is that of the test element plus `ς • 1`.
    rw [InvExtBlock.rhoAlg_entries] at hrho
    have h00 := congrFun (congrFun hrho 0) 0
    simpa [Matrix.one_apply] using h00

/-- **The outside transform of the regularised element**, explicitly.
`V(ς) = -ς/2` at the trivial character, and independent of `ς` elsewhere.

The `ς`-independence for `k ≠ 0` is what lets a single `ζ` of modulus one serve
for all `ς ≥ 0`: the identity matrix contributes nothing to the `(1,0)`
entry. -/
theorem Vblock_regTestElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    (ε ς : ℝ) (k : ZMod n) :
    InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)
      = if k = 0 then ((-(ς / 2) : ℝ) : ℂ)
        else InvExtBlock.Vblock (testElement n K ε) (0 : ZMod n) (chi k) := by
  -- Use the `(0,1)` entry, not the `(1,0)` one. `rhoAlg_entries` gives `(0,1)` as
  -- `χ z * V`, and here `z = 0` with `χ 0 = 1`, so it *is* `V` — no conjugation
  -- to undo. The `(1,0)` entry is `conj V` and forces a conjugate-injectivity
  -- step that buys nothing.
  have hz : (chi k) (0 : ZMod n) = 1 := (chi k).map_zero_eq_one
  have hrho := rhoAlg_regTestElement (n := n) hK hn ε ς k
  rw [InvExtBlock.rhoAlg_entries] at hrho
  split_ifs at hrho ⊢ with hk
  · have h01 := congrFun (congrFun hrho 0) 1
    simpa [hz] using h01
  · rw [InvExtBlock.rhoAlg_entries] at hrho
    have h01 := congrFun (congrFun hrho 0) 1
    simpa [hz, Matrix.one_apply] using h01

/-! ### From block entries back to coefficients

The reduction from coefficients to block entries holds for *any* family of
group-algebra elements indexed by `ς` — nothing about the test element enters, so
it is stated at that generality. -/

section StepOne

variable {A : Type*} [AddCommGroup A] [Fintype A] {z : A} [Fact (z + z = 0)]
  [DecidableEq A]

/-- **Coefficientwise convergence follows from blockwise convergence.**

If every abelian transform `U^{y ς}(ψ)` and every outside transform
`V^{y ς, d}(ψ)` converges along a filter `l`, then every *coefficient* of `y ς`
converges to the corresponding coefficient of the limit element.

The proof uses only Fourier inversion and finiteness of the dual, so no
hypothesis about `y` is needed beyond the two convergences.

The mechanism: `Lyons.AddCharFourier.dft_inversion` writes each coefficient as
`|A|⁻¹` times a finite sum over the dual of a transform value against a character
value, the sum is over a `Fintype`, and `Complex.re` is continuous. `InvExt` has
two constructors, so `g` splits into the `rot` case (governed by `U`) and the
`refl` case (governed by `V`, after shifting the index by `d`). -/
theorem tendsto_co_of_tendsto_blocks {l : Filter ℝ}
    {y : ℝ → MonoidAlgebra ℝ (InvExt A z)} {y₀ : MonoidAlgebra ℝ (InvExt A z)}
    (d : A)
    (hU : ∀ ψ : AddChar A ℂ,
      Filter.Tendsto (fun ς => InvExtBlock.Ublock (y ς) ψ) l
        (nhds (InvExtBlock.Ublock y₀ ψ)))
    (hV : ∀ ψ : AddChar A ℂ,
      Filter.Tendsto (fun ς => InvExtBlock.Vblock (y ς) d ψ) l
        (nhds (InvExtBlock.Vblock y₀ d ψ)))
    (g : InvExt A z) :
    Filter.Tendsto (fun ς => co (y ς) g) l (nhds (co y₀ g)) := by
  -- Inversion turns a coefficient into a finite sum of transform values.
  have inv_u : ∀ (x : MonoidAlgebra ℝ (InvExt A z)) (a : A),
      ((co x (InvExt.rot a) : ℝ) : ℂ)
        = (Fintype.card A : ℂ)⁻¹
            * ∑ ψ : AddChar A ℂ, InvExtBlock.Ublock x ψ * conj (ψ a) :=
    fun x a => AddCharFourier.dft_inversion (InvExtBlock.uCoeff x) a
  have inv_v : ∀ (x : MonoidAlgebra ℝ (InvExt A z)) (a : A),
      ((co x (InvExt.refl (a + d)) : ℝ) : ℂ)
        = (Fintype.card A : ℂ)⁻¹
            * ∑ ψ : AddChar A ℂ, InvExtBlock.Vblock x d ψ * conj (ψ a) :=
    fun x a => AddCharFourier.dft_inversion (InvExtBlock.vCoeff x d) a
  -- A finite sum of convergent terms converges, then scale and take the real part.
  have key : ∀ (a : A)
      (T : MonoidAlgebra ℝ (InvExt A z) → AddChar A ℂ → ℂ),
      (∀ ψ, Filter.Tendsto (fun ς => T (y ς) ψ) l (nhds (T y₀ ψ))) →
      Filter.Tendsto (fun ς => (Fintype.card A : ℂ)⁻¹
          * ∑ ψ : AddChar A ℂ, T (y ς) ψ * conj (ψ a)) l
        (nhds ((Fintype.card A : ℂ)⁻¹
          * ∑ ψ : AddChar A ℂ, T y₀ ψ * conj (ψ a))) := by
    intro a T hT
    exact (tendsto_finset_sum _ fun ψ _ => (hT ψ).mul_const _).const_mul _
  -- `Filter.tendsto_ofReal_iff` transfers the ℂ-valued convergence back to ℝ
  -- directly. Composing with `Complex.continuous_re` instead leaves a
  -- `(↑r).re` that `simpa` would then have to unwind, which is where an earlier
  -- attempt at this got stuck.
  cases g with
  | rot a =>
    have h := key a (fun x ψ => InvExtBlock.Ublock x ψ) hU
    have h' : Filter.Tendsto (fun ς => ((co (y ς) (InvExt.rot a) : ℝ) : ℂ)) l
        (nhds ((co y₀ (InvExt.rot a) : ℝ) : ℂ)) := by
      simpa only [inv_u] using h
    exact Filter.tendsto_ofReal_iff.mp h'
  | refl a =>
    -- Shift the index: `refl a = refl ((a - d) + d)`, which is what `V` sees.
    have hshift : a = (a - d) + d := by abel
    have h := key (a - d) (fun x ψ => InvExtBlock.Vblock x d ψ) hV
    have h' : Filter.Tendsto
        (fun ς => ((co (y ς) (InvExt.refl ((a - d) + d)) : ℝ) : ℂ)) l
        (nhds ((co y₀ (InvExt.refl ((a - d) + d)) : ℝ) : ℂ)) := by
      simpa only [inv_v] using h
    rw [hshift]
    exact Filter.tendsto_ofReal_iff.mp h'

/-- **A blockwise bound bounds every coefficient**, with no loss.

If `‖U^y(ψ)‖ ≤ M` and `‖V^{y,d}(ψ)‖ ≤ M` for every character `ψ`, then
`|y_g| ≤ M` for every `g`.

The companion of `Lyons.Converse.tendsto_co_of_tendsto_blocks`, by the same
Fourier inversion and in the same two cases: a coefficient is `|A|⁻¹` times a sum
of `|A|` terms, each a transform value against a character value of modulus one
(`Lyons.AddCharFourier.norm_char_apply`). So the bound passes through the average
unchanged — there is no factor of `|A|` to pay, which is what makes this usable
as the `hbound` of `Lyons.tendsto_intervalIntegral_of_dominated`. -/
theorem abs_co_le_of_blocks_le {y : MonoidAlgebra ℝ (InvExt A z)} (d : A) {M : ℝ}
    (hU : ∀ ψ : AddChar A ℂ, ‖InvExtBlock.Ublock y ψ‖ ≤ M)
    (hV : ∀ ψ : AddChar A ℂ, ‖InvExtBlock.Vblock y d ψ‖ ≤ M)
    (g : InvExt A z) : |co y g| ≤ M := by
  have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have := Fintype.card_pos_iff.mpr (⟨0⟩ : Nonempty A)
    exact_mod_cast this
  -- The averaging step, once, for either transform.
  have key : ∀ (a : A) (T : AddChar A ℂ → ℂ), (∀ ψ, ‖T ψ‖ ≤ M) →
      ‖(Fintype.card A : ℂ)⁻¹ * ∑ ψ : AddChar A ℂ, T ψ * conj (ψ a)‖ ≤ M := by
    intro a T hT
    have hnorm : ‖∑ ψ : AddChar A ℂ, T ψ * conj (ψ a)‖
        ≤ (Fintype.card A : ℝ) * M := by
      refine (norm_sum_le _ _).trans ?_
      have hcards : (Finset.univ : Finset (AddChar A ℂ)).card = Fintype.card A := by
        rw [Finset.card_univ]; exact AddChar.card_eq
      calc ∑ ψ : AddChar A ℂ, ‖T ψ * conj (ψ a)‖
          ≤ ∑ _ψ : AddChar A ℂ, M := by
            refine Finset.sum_le_sum fun ψ _ => ?_
            rw [norm_mul, RCLike.norm_conj, AddCharFourier.norm_char_apply, mul_one]
            exact hT ψ
        _ = (Fintype.card A : ℝ) * M := by
            rw [Finset.sum_const, hcards, nsmul_eq_mul]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hcard]
    exact hnorm
  cases g with
  | rot a =>
    have hinv : ((co y (InvExt.rot a) : ℝ) : ℂ)
        = (Fintype.card A : ℂ)⁻¹
            * ∑ ψ : AddChar A ℂ, InvExtBlock.Ublock y ψ * conj (ψ a) :=
      AddCharFourier.dft_inversion (InvExtBlock.uCoeff y) a
    have h := key a (fun ψ => InvExtBlock.Ublock y ψ) hU
    rw [← hinv, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  | refl a =>
    have hshift : a = (a - d) + d := by abel
    have hinv : ((co y (InvExt.refl ((a - d) + d)) : ℝ) : ℂ)
        = (Fintype.card A : ℂ)⁻¹
            * ∑ ψ : AddChar A ℂ, InvExtBlock.Vblock y d ψ * conj (ψ (a - d)) :=
      AddCharFourier.dft_inversion (InvExtBlock.vCoeff y d) (a - d)
    have h := key (a - d) (fun ψ => InvExtBlock.Vblock y d ψ) hV
    rw [← hinv, Complex.norm_real, Real.norm_eq_abs] at h
    rw [hshift]
    exact h

end StepOne

/-! ### The modulus-one factor

`Lyons.rhoAlg_sandwich` takes the outside transform in the form `ζ * w` with
`‖ζ‖ = 1` and `w ≥ 0`. Producing such a `ζ` is the polar decomposition of a single
complex number, and it is worth isolating because one `ζ` has to serve
*simultaneously for every `ς`* — which is possible exactly because
`Vblock` is `ς`-independent off the trivial character (`Vblock_regTestElement`) and
is `-(ς/2)` on it, so `ζ = -1` works there for every `ς ≥ 0`. -/

/-- **Polar form of a complex number against its own modulus.** Every `v` is
`ζ * ‖v‖` for some `ζ` of modulus one; at `v = 0` any `ζ` does, and `1` is taken.

This is the shape `Lyons.rhoAlg_sandwich` wants its `hV` hypothesis in. -/
theorem exists_unit_mul_norm (v : ℂ) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ v = ζ * (‖v‖ : ℂ) := by
  by_cases hv : v = 0
  · exact ⟨1, by simp, by simp [hv]⟩
  · refine ⟨v / (‖v‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      exact div_self (norm_ne_zero_iff.mpr hv)
    · rw [div_mul_cancel₀]
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)

/-! ### The block data is continuous in `ς`

`Lyons.rhoAlg_sandwich` writes each entry of the sandwich's block as a fixed
polynomial in the four block powers formed from `U` and `w`. Those are continuous
in `(U, w)` by `Lyons.continuous_bpAlpha` and friends, so all that is left is that
`ς ↦ (U(ς), w(ς))` is continuous — which the closed forms above make immediate,
both being affine in `ς` up to an absolute value. -/

/-- The real abelian transform of the regularised element at `χ_k`. Real because
the element is self-adjoint (`invol_regTestElement`), so `conj_Ublock` applies. -/
private noncomputable def Ureg (K : ℤ) (ε : ℝ) (k : ZMod n) (ς : ℝ) : ℝ :=
  (InvExtBlock.Ublock (regTestElement n K ε ς) (chi k)).re

/-- The modulus of the outside transform of the regularised element at `χ_k`. -/
private noncomputable def wreg (K : ℤ) (ε : ℝ) (k : ZMod n) (ς : ℝ) : ℝ :=
  ‖InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)‖

/-- **`U(ς)` is continuous**, being `ς/2` at the trivial character and `U(0) + ς`
elsewhere — affine either way. -/
theorem continuous_Ureg {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε : ℝ)
    (k : ZMod n) : Continuous (Ureg (n := n) K ε k) := by
  by_cases hk : k = 0
  · have h : Ureg (n := n) K ε k = fun ς : ℝ => ς / 2 := funext fun ς => by
      rw [Ureg, Ublock_regTestElement hK hn ε ς k, if_pos hk]; simp
    rw [h]; fun_prop
  · have h : Ureg (n := n) K ε k
        = fun ς : ℝ => (InvExtBlock.Ublock (testElement n K ε) (chi k)).re + ς :=
      funext fun ς => by
        rw [Ureg, Ublock_regTestElement hK hn ε ς k, if_neg hk]; simp
    rw [h]; fun_prop

/-- **`w(ς)` is continuous**, being `|ς/2|` at the trivial character and constant
elsewhere, since `V` does not depend on `ς` there. -/
theorem continuous_wreg {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε : ℝ)
    (k : ZMod n) : Continuous (wreg (n := n) K ε k) := by
  -- `wreg` is by definition a norm, so prove `Vblock` continuous and compose.
  -- Converting the `k = 0` value to `|ς/2|` first is a detour that then needs the
  -- norm-of-a-real-coercion rewritten, and that is where this got stuck twice.
  have hV : Continuous fun ς : ℝ =>
      InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k) := by
    by_cases hk : k = 0
    · subst hk
      have h : (fun ς : ℝ =>
            InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi 0))
          = fun ς : ℝ => ((-(ς / 2) : ℝ) : ℂ) := funext fun ς => by
        rw [Vblock_regTestElement hK hn ε ς 0, if_pos rfl]
      rw [h]; fun_prop
    · have h : (fun ς : ℝ =>
            InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k))
          = fun _ : ℝ =>
            InvExtBlock.Vblock (testElement n K ε) (0 : ZMod n) (chi k) :=
        funext fun ς => by rw [Vblock_regTestElement hK hn ε ς k, if_neg hk]
      rw [h]; fun_prop
  exact hV.norm

/-- **The block data is continuous in `ς`**, as a pair. Composing with
`Lyons.continuous_bpAlpha` and friends makes each block power, and hence by
`Lyons.rhoAlg_sandwich` each entry of the sandwich's block, continuous in `ς`. -/
theorem continuous_blockData {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε : ℝ)
    (k : ZMod n) :
    Continuous fun ς : ℝ => (Ureg (n := n) K ε k ς, wreg (n := n) K ε k ς) :=
  (continuous_Ureg hK hn ε k).prodMk (continuous_wreg hK hn ε k)

/-! ### The remaining two side conditions of `rhoAlg_sandwich`

`Lyons.rhoAlg_sandwich` consumes the block data as a *real* `U` with
`((U : ℝ) : ℂ) = Ublock x χ`, and a *nonnegative* `w`. Both hold for the
regularised element for structural reasons rather than by computation, so they are
recorded here next to the data they are about. -/

/-- **`U(ς)` really is the abelian transform.** The regularised element is
self-adjoint (`invol_regTestElement`), so `Ublock` is real (`conj_Ublock`) and
therefore equal to the coercion of its own real part — which is how `Ureg` is
defined.

This is `rhoAlg_sandwich`'s `hU` hypothesis for this family. -/
theorem ofReal_Ureg (K : ℤ) (ε : ℝ) (k : ZMod n) (ς : ℝ) :
    ((Ureg (n := n) K ε k ς : ℝ) : ℂ)
      = InvExtBlock.Ublock (regTestElement n K ε ς) (chi k) :=
  InvExtBlock.Ublock_ofReal_re _ (invol_regTestElement K ε ς) _

/-- **`w(ς)` is nonnegative**, being a norm. `rhoAlg_sandwich`'s `hw`
hypothesis. -/
theorem wreg_nonneg (K : ℤ) (ε : ℝ) (k : ZMod n) (ς : ℝ) :
    0 ≤ wreg (n := n) K ε k ς :=
  norm_nonneg _

/-! ### Assembling the two transforms of the sandwich

Only two entries of the sandwich's block are needed: `Ublock` is the `(0,0)`
entry and `Vblock` the `(0,1)` one (the latter because `rhoAlg_entries` gives it
as `χ z * V` and `z = 0`). So rather than rewrite the whole `2 × 2` literal of
`rhoAlg_sandwich`, each is extracted by `congrFun` and is a polynomial in the four
block powers with `ζ`-built, `ς`-independent coefficients. -/

section Node

variable {K : ℤ} {ε θ : ℝ}

/-- The `(0,0)` and `(0,1)` entries of the sandwich's block, as explicit
functions of the block data. -/
private noncomputable def UPoly (ζ : ℂ) (U w θ : ℝ) : ℂ :=
  ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ)
    + conj ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ)

private noncomputable def VPoly (ζ : ℂ) (U w θ : ℝ) : ℂ :=
  ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
    + ζ ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ)

private theorem continuous_UPoly (ζ : ℂ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    Continuous fun p : ℝ × ℝ => UPoly ζ p.1 p.2 θ := by
  have hb := continuous_bpBeta (θ := θ) hθ
  have hg := continuous_bpGamma (θ := θ) hθ'
  have ha := continuous_bpAlpha (θ := θ) hθ
  have hd := continuous_bpDelta (θ := θ) hθ'
  unfold UPoly
  fun_prop (disch := assumption)

private theorem continuous_VPoly (ζ : ℂ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    Continuous fun p : ℝ × ℝ => VPoly ζ p.1 p.2 θ := by
  have hb := continuous_bpBeta (θ := θ) hθ
  have hg := continuous_bpGamma (θ := θ) hθ'
  have ha := continuous_bpAlpha (θ := θ) hθ
  have hd := continuous_bpDelta (θ := θ) hθ'
  unfold VPoly
  fun_prop (disch := assumption)

/-! ### The two entries are bounded by the block data itself

The bound `hbound` needs, and it comes out sharp. Each of the four products is
at most `U + w`, which alone would bound every entry by `2(U + w)`. But the two
relations `Lyons.bp_rel_diag` and `Lyons.bp_rel_off` say more than that: with all
four
powers nonnegative, `αγ + βδ = U` and `αδ + βγ = w` exhibit each entry's two
products as a *partition* of `U` or of `w`. Since `‖ζ‖ = ‖conj ζ‖ = ‖ζ²‖ = 1`,
the triangle inequality then gives `‖UPoly‖ ≤ w` and `‖VPoly‖ ≤ U` on the nose —
no factor of `2`, and no `U + w`. -/

/-- **The sandwich's abelian entry is bounded by `w`.** The two products in
`UPoly` are `βγ` and `αδ`, whose sum is exactly `w` by `Lyons.bp_rel_off`; both
are nonnegative by `Lyons.bp_nonneg`, and the two unit factors `ζ`, `conj ζ`
contribute nothing. -/
private theorem norm_UPoly_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) {U w : ℝ} (hw : 0 ≤ w)
    (hUw : w ≤ U) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) : ‖UPoly ζ U w θ‖ ≤ w := by
  obtain ⟨ha, hb, hg, hd⟩ := bp_nonneg hw hUw hθ hθ'
  have hsum := bp_rel_off (U := U) (w := w) (θ := θ) hw hUw
  have hbg : (0 : ℝ) ≤ bpBeta U w θ * bpGamma U w θ := mul_nonneg hb hg
  have had : (0 : ℝ) ≤ bpAlpha U w θ * bpDelta U w θ := mul_nonneg ha hd
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hζ, RCLike.norm_conj, hζ, one_mul, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hbg, abs_of_nonneg had]
  linarith

/-- **The sandwich's outside entry is bounded by `U`.** The two products in
`VPoly` are `αγ` and `βδ`, whose sum is exactly `U` by `Lyons.bp_rel_diag`. -/
private theorem norm_VPoly_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) {U w : ℝ} (hw : 0 ≤ w)
    (hUw : w ≤ U) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) : ‖VPoly ζ U w θ‖ ≤ U := by
  obtain ⟨ha, hb, hg, hd⟩ := bp_nonneg hw hUw hθ hθ'
  have hsum := bp_rel_diag (U := U) (w := w) (θ := θ) hw hUw
  have hag : (0 : ℝ) ≤ bpAlpha U w θ * bpGamma U w θ := mul_nonneg ha hg
  have hbd : (0 : ℝ) ≤ bpBeta U w θ * bpDelta U w θ := mul_nonneg hb hd
  have hz2 : ‖ζ ^ 2‖ = 1 := by rw [norm_pow, hζ, one_pow]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hz2, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hag, abs_of_nonneg hbd]
  linarith

/-- **`UPoly` is continuous in `θ` on `(0, 1)`**, the block data held fixed.
Open interval, for the reason given in `Lyons.Dihedral.BlockPowersCont`: at
the trivial character `U = w = ς/2`, so `U - w = 0` and the powers jump at the
endpoints. -/
private theorem continuousOn_UPoly_exponent (ζ : ℂ) (U w : ℝ) :
    ContinuousOn (fun t : ℝ => UPoly ζ U w t) (Set.Ioo 0 1) := by
  have hb := continuousOn_bpBeta_exponent U w
  have hg := continuousOn_bpGamma_exponent U w
  have ha := continuousOn_bpAlpha_exponent U w
  have hd := continuousOn_bpDelta_exponent U w
  unfold UPoly
  exact (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (hb.mul hg))).add
    (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (ha.mul hd)))

/-- **`VPoly` is continuous in `θ` on `(0, 1)`.** -/
private theorem continuousOn_VPoly_exponent (ζ : ℂ) (U w : ℝ) :
    ContinuousOn (fun t : ℝ => VPoly ζ U w t) (Set.Ioo 0 1) := by
  have hg := continuousOn_bpGamma_exponent U w
  have ha := continuousOn_bpAlpha_exponent U w
  have hb := continuousOn_bpBeta_exponent U w
  have hd := continuousOn_bpDelta_exponent U w
  unfold VPoly
  exact (Complex.continuous_ofReal.comp_continuousOn (ha.mul hg)).add
    (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (hb.mul hd)))

/-- **The sandwich's abelian transform, in terms of the block data.**
`rhoAlg_sandwich` with every side condition discharged for this family, then read
off the `(0,0)` entry. -/
private theorem Ublock_sandwich_reg {n : ℕ} [NeZero n] {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    {ς : ℝ} (hς : 0 ≤ ς) (k : ZMod n) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hV : InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)
        = ζ * ((wreg (n := n) K ε k ς : ℝ) : ℂ)) :
    InvExtBlock.Ublock
        (sandwich (regTestElement n K ε ς) (InvExt.b : InvExt (ZMod n) 0) θ) (chi k)
      = UPoly ζ (Ureg (n := n) K ε k ς) (wreg (n := n) K ε k ς) θ := by
  have hz : (chi k) (0 : ZMod n) = 1 := (chi k).map_zero_eq_one
  have hsw := InvExtBlock.rhoAlg_sandwich (chi k) (0 : ZMod n) (regTestElement n K ε ς)
    (isPos_regTestElement hK hn hε hς) hθ hθ' hz hζ (wreg_nonneg K ε k ς)
    (ofReal_Ureg K ε k ς) hV
  rw [InvExtBlock.rhoAlg_entries] at hsw
  have h00 := congrFun (congrFun hsw 0) 0
  simpa [UPoly, InvExt.b] using h00

/-- **The sandwich's outside transform, in terms of the block data.** The `(0,1)`
entry, which `rhoAlg_entries` gives as `χ z * V` — and `z = 0` here, so it is
`V`. -/
private theorem Vblock_sandwich_reg {n : ℕ} [NeZero n] {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    {ς : ℝ} (hς : 0 ≤ ς) (k : ZMod n) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hV : InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)
        = ζ * ((wreg (n := n) K ε k ς : ℝ) : ℂ)) :
    InvExtBlock.Vblock
        (sandwich (regTestElement n K ε ς) (InvExt.b : InvExt (ZMod n) 0) θ)
        (0 : ZMod n) (chi k)
      = VPoly ζ (Ureg (n := n) K ε k ς) (wreg (n := n) K ε k ς) θ := by
  have hz : (chi k) (0 : ZMod n) = 1 := (chi k).map_zero_eq_one
  have hsw := InvExtBlock.rhoAlg_sandwich (chi k) (0 : ZMod n) (regTestElement n K ε ς)
    (isPos_regTestElement hK hn hε hς) hθ hθ' hz hζ (wreg_nonneg K ε k ς)
    (ofReal_Ureg K ε k ς) hV
  rw [InvExtBlock.rhoAlg_entries] at hsw
  have h01 := congrFun (congrFun hsw 0) 1
  simpa [VPoly, hz, InvExt.b] using h01

/-- At `ς = 0` the regularised element is the test element. -/
private theorem regTestElement_zero {n : ℕ} [NeZero n] (K : ℤ) (ε : ℝ) :
    regTestElement n K ε 0 = testElement n K ε := by
  simp [regTestElement]

/-- **One modulus-one `ζ` serving every `ς ≥ 0` at once.**

Off the trivial character `Vblock` does not depend on `ς` at all, so any polar
factor for its
single value works throughout; on the trivial character `Vblock = -(ς/2)` while
`w = ς/2` for `ς ≥ 0`, so `ζ = -1` works throughout. The sign hypothesis is
exactly what turns `|ς/2|` into `ς/2`. -/
private theorem exists_zeta_uniform {n : ℕ} [NeZero n] {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) (ε : ℝ) (k : ZMod n) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ ς : ℝ, 0 ≤ ς →
      InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)
        = ζ * ((wreg (n := n) K ε k ς : ℝ) : ℂ) := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨-1, by simp, fun ς hς => ?_⟩
    have hv : InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi 0)
        = ((-(ς / 2) : ℝ) : ℂ) := by
      rw [Vblock_regTestElement hK hn ε ς 0, if_pos rfl]
    have hw : wreg (n := n) K ε 0 ς = ς / 2 := by
      rw [wreg, hv, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ς / 2)]
    rw [hv, hw]
    push_cast
    ring
  · obtain ⟨ζ, hζ, hpolar⟩ :=
      exists_unit_mul_norm
        (InvExtBlock.Vblock (testElement n K ε) (0 : ZMod n) (chi k))
    refine ⟨ζ, hζ, fun ς _ => ?_⟩
    have hv : InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)
        = InvExtBlock.Vblock (testElement n K ε) (0 : ZMod n) (chi k) := by
      rw [Vblock_regTestElement hK hn ε ς k, if_neg hk]
    have hw : wreg (n := n) K ε k ς
        = ‖InvExtBlock.Vblock (testElement n K ε) (0 : ZMod n) (chi k)‖ := by
      rw [wreg, hv]
    rw [hv, hw]
    exact hpolar

/-- Blockwise convergence for one transform, packaged so both `U` and `V` can use
it. `P` is the entry polynomial, `T` the transform, and `hEq` the closed form
valid for `ς ≥ 0`. -/
private theorem tendsto_transform {n : ℕ} [NeZero n] {K : ℤ} {ε θ : ℝ}
    (k : ZMod n) (ζ : ℂ)
    (P : ℂ → ℝ → ℝ → ℝ → ℂ) (T : MonoidAlgebra ℝ (InvExt (ZMod n) 0) → ℂ)
    (hP : Continuous fun p : ℝ × ℝ => P ζ p.1 p.2 θ)
    (hdata : Continuous fun ς : ℝ =>
      (Ureg (n := n) K ε k ς, wreg (n := n) K ε k ς))
    (hEq : ∀ ς : ℝ, 0 ≤ ς →
      T (sandwich (regTestElement n K ε ς) (InvExt.b : InvExt (ZMod n) 0) θ)
        = P ζ (Ureg (n := n) K ε k ς) (wreg (n := n) K ε k ς) θ) :
    Filter.Tendsto
      (fun ς => T (sandwich (regTestElement n K ε ς)
        (InvExt.b : InvExt (ZMod n) 0) θ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T (sandwich (testElement n K ε)
        (InvExt.b : InvExt (ZMod n) 0) θ))) := by
  -- The composite is continuous, hence continuous within `Ioi 0` at `0`.
  have hcomp : Filter.Tendsto
      (fun ς : ℝ => P ζ (Ureg (n := n) K ε k ς) (wreg (n := n) K ε k ς) θ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (P ζ (Ureg (n := n) K ε k 0) (wreg (n := n) K ε k 0) θ)) :=
    ((hP.comp hdata).continuousAt).continuousWithinAt
  -- The limit value is the transform at `ς = 0`, since `x₀ = ξ` there.
  have hval : P ζ (Ureg (n := n) K ε k 0) (wreg (n := n) K ε k 0) θ
      = T (sandwich (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0) θ) := by
    rw [← hEq 0 le_rfl, regTestElement_zero]
  rw [← hval]
  -- On `Ioi 0` the two functions agree, so the limits do.
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ς hς
  exact (hEq ς (le_of_lt hς)).symm

/-- **The sandwich's coefficients converge as the regularisation vanishes.**

For every `g`, the coefficient of `𝓢_{ξ_{n,K,ε,ς},θ,τ}` at `g` tends to that of
`𝓢_{ξ_{n,K,ε},θ,τ}` as `ς → 0⁺`.

`C` is `ZMod n` written additively, so `z = 0` and `d = 0`, and `τ` is
`Lyons.InvExt.b`. The conditions on `K` and `n` appear as `2 ≤ K` and
`2 * K < n`, inherited from `rhoAlg_regTestElement`. The limit is expressed with
`nhdsWithin 0 (Set.Ioi 0)`, the idiom `Lyons.Converse.EnergyFormula` uses
for `→ 0⁺`.

Three ingredients, each proved separately above: `tendsto_co_of_tendsto_blocks`
reduces coefficients to block transforms; `Ublock_sandwich_reg` /
`Vblock_sandwich_reg` put each transform in closed form as a polynomial in the
block data; and `continuous_blockData` with `continuous_UPoly` /
`continuous_VPoly` make that polynomial continuous in `ς`. The characters are
transferred from the enumerated `χ_k` to an arbitrary `ψ` by
`cyclicAddChar_bijective`. -/
@[lyons_tag "lem_x_eps_reg_sandwich_limit"]
theorem tendsto_co_sandwich_regTestElement {n : ℕ} [NeZero n] {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (g : InvExt (ZMod n) 0) :
    Filter.Tendsto
      (fun ς => co (sandwich (regTestElement n K ε ς)
        (InvExt.b : InvExt (ZMod n) 0) θ) g)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (co (sandwich (testElement n K ε)
        (InvExt.b : InvExt (ZMod n) 0) θ) g)) := by
  -- Rewrite the limit point as the `ς = 0` member of the family.
  rw [show testElement n K ε = regTestElement n K ε 0 from
    (regTestElement_zero K ε).symm]
  refine tendsto_co_of_tendsto_blocks (0 : ZMod n) (fun ψ => ?_) (fun ψ => ?_) g
  · -- Transfer `ψ` to some `χ_k`, then apply the packaged convergence.
    obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    obtain ⟨ζ, hζ, hzeta⟩ := exists_zeta_uniform (n := n) hK hn ε k
    rw [← hk, regTestElement_zero]
    exact tendsto_transform k ζ UPoly
      (fun x => InvExtBlock.Ublock x (chi k))
      (continuous_UPoly ζ hθ hθ') (continuous_blockData hK hn ε k)
      (fun ς hς => Ublock_sandwich_reg hK hn hε hθ hθ' hς k hζ (hzeta ς hς))
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    obtain ⟨ζ, hζ, hzeta⟩ := exists_zeta_uniform (n := n) hK hn ε k
    rw [← hk, regTestElement_zero]
    exact tendsto_transform k ζ VPoly
      (fun x => InvExtBlock.Vblock x (0 : ZMod n) (chi k))
      (continuous_VPoly ζ hθ hθ') (continuous_blockData hK hn ε k)
      (fun ς hς => Vblock_sandwich_reg hK hn hε hθ hθ' hς k hζ (hzeta ς hς))

/-- **The coefficients of the regularised element are continuous in `ς`.**

Distinct from `tendsto_co_sandwich_regTestElement`, which is about the
coefficients of its *sandwich*. The energy limit needs both: its integrand is
`J_p(x_ς)_g · ((𝓢_{x_ς,θ,τ})_g − (x_ς)_g)`, so the element's own coefficients
appear twice, once inside `J_p`.

Immediate from the definition — `ξ_{n,K,ε,ς} = ξ_{n,K,ε} + ς(1 − π_G)` is affine
in `ς`, so each coefficient is. -/
theorem continuous_co_regTestElement {n : ℕ} [NeZero n] (K : ℤ) (ε : ℝ)
    (g : InvExt (ZMod n) 0) :
    Continuous fun ς : ℝ => co (regTestElement n K ε ς) g := by
  have h : (fun ς : ℝ => co (regTestElement n K ε ς) g)
      = fun ς : ℝ => co (testElement n K ε) g
          + ς * co ((1 : MonoidAlgebra ℝ (InvExt (ZMod n) 0))
              - uniform (InvExt (ZMod n) 0)) g := by
    funext ς
    rw [regTestElement, co_add, co_smul]
  rw [h]
  fun_prop

/-- The `ς → 0⁺` form, which is what the energy limit consumes. -/
theorem tendsto_co_regTestElement {n : ℕ} [NeZero n] (K : ℤ) (ε : ℝ)
    (g : InvExt (ZMod n) 0) :
    Filter.Tendsto (fun ς => co (regTestElement n K ε ς) g)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (co (testElement n K ε) g)) := by
  rw [show co (testElement n K ε) g = co (regTestElement n K ε 0) g from
    by rw [regTestElement_zero]]
  exact ((continuous_co_regTestElement K ε g).continuousAt).continuousWithinAt

/-- **The energy integrand converges pointwise in `θ`** as the regularisation
vanishes.

This is the `hlim` hypothesis of `Lyons.tendsto_intervalIntegral_of_dominated`
for the energy limit: the integrand of `Lyons.Converse.energy` at the regularised
element tends to the integrand at the test element, for each fixed `θ`.

Three convergences multiply out, one per factor:

* `tendsto_co_regTestElement` — the element's own coefficients, inside `J_p` and
  as the subtrahend;
* `tendsto_co_sandwich_regTestElement` — the sandwich's coefficients;
* `continuousAt_signedPow` — `J_p` is continuous at each `(ξ)_g`, **which is
  where the nonvanishing hypothesis is used**. `J_p` is discontinuous at `0` when
  `p = 1`, so `hne` is not a convenience: without it the composition fails at
  exactly the exponent the failure of rate-monotonicity cares most about.

The sum is over a `Fintype`, so `tendsto_finset_sum` finishes. -/
theorem tendsto_energyIntegrand {n : ℕ} [NeZero n] {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ)
    (hne : ∀ g : InvExt (ZMod n) 0, co (testElement n K ε) g ≠ 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    Filter.Tendsto
      (fun ς => ∑ g : InvExt (ZMod n) 0,
        signedPow p (co (regTestElement n K ε ς) g)
          * (co (sandwich (regTestElement n K ε ς)
                (InvExt.b : InvExt (ZMod n) 0) θ) g
              - co (regTestElement n K ε ς) g))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ g : InvExt (ZMod n) 0,
        signedPow p (co (testElement n K ε) g)
          * (co (sandwich (testElement n K ε)
                (InvExt.b : InvExt (ZMod n) 0) θ) g
              - co (testElement n K ε) g))) := by
  refine tendsto_finset_sum _ fun g _ => ?_
  have hco := tendsto_co_regTestElement (n := n) K ε g
  have hsw := tendsto_co_sandwich_regTestElement (n := n) hK hn hε hθ hθ' g
  have hJ : Filter.Tendsto
      (fun ς => signedPow p (co (regTestElement n K ε ς) g))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (signedPow p (co (testElement n K ε) g))) :=
    ((continuousAt_signedPow p (hne g)).tendsto).comp hco
  exact hJ.mul (hsw.sub hco)

end Node

/-! ### The two side conditions of dominated convergence

`Lyons.tendsto_intervalIntegral_of_dominated` takes three hypotheses. `hlim` is
`tendsto_energyIntegrand` above. The other two are here: measurability of the
integrand in `θ`, and a bound uniform in both variables. Both are consequences of
the block machinery already built, and neither needs any new analysis. -/

section SideConditions

variable {n : ℕ} [NeZero n]

/-- **The sandwich's coefficients are continuous in `θ` on `(0, 1)`**, at fixed
regularisation.

Same three steps as `tendsto_co_sandwich_regTestElement`, along a different
filter: `tendsto_co_of_tendsto_blocks` is stated for an arbitrary filter, so it
serves for `𝓝[Ioo 0 1] θ₀` exactly as it did for `𝓝[>] 0`. What moves is which
argument is held fixed — there the exponent, here the regularisation.

The interval is open because the block powers genuinely jump at both endpoints
when `U = w`, which happens at the trivial character for every `ς`; see
`Lyons.Dihedral.BlockPowersCont`. -/
theorem continuousOn_co_sandwich_regTestElement {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {ς : ℝ} (hς : 0 ≤ ς)
    (g : InvExt (ZMod n) 0) :
    ContinuousOn (fun θ : ℝ => co (sandwich (regTestElement n K ε ς)
      (InvExt.b : InvExt (ZMod n) 0) θ) g) (Set.Ioo 0 1) := by
  intro θ₀ hθ₀
  -- The closed form of a transform, valid throughout the open interval.
  have hform : ∀ (k : ZMod n) (ζ : ℂ), ‖ζ‖ = 1 →
      (InvExtBlock.Vblock (regTestElement n K ε ς) (0 : ZMod n) (chi k)
        = ζ * ((wreg (n := n) K ε k ς : ℝ) : ℂ)) →
      (∀ t ∈ Set.Ioo (0 : ℝ) 1,
          InvExtBlock.Ublock (sandwich (regTestElement n K ε ς)
            (InvExt.b : InvExt (ZMod n) 0) t) (chi k)
            = UPoly ζ (Ureg (n := n) K ε k ς) (wreg (n := n) K ε k ς) t)
        ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          InvExtBlock.Vblock (sandwich (regTestElement n K ε ς)
            (InvExt.b : InvExt (ZMod n) 0) t) (0 : ZMod n) (chi k)
            = VPoly ζ (Ureg (n := n) K ε k ς) (wreg (n := n) K ε k ς) t := by
    intro k ζ hζ hV
    exact ⟨fun t ht => Ublock_sandwich_reg hK hn hε ht.1.le ht.2.le hς k hζ hV,
      fun t ht => Vblock_sandwich_reg hK hn hε ht.1.le ht.2.le hς k hζ hV⟩
  refine tendsto_co_of_tendsto_blocks (0 : ZMod n) (fun ψ => ?_) (fun ψ => ?_) g
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    obtain ⟨ζ, hζ, hzeta⟩ := exists_zeta_uniform (n := n) hK hn ε k
    obtain ⟨hU, -⟩ := hform k ζ hζ (hzeta ς hς)
    rw [← hk, hU θ₀ hθ₀]
    refine Filter.Tendsto.congr' ?_ ((continuousOn_UPoly_exponent ζ _ _) θ₀ hθ₀).tendsto
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hU t ht).symm
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    obtain ⟨ζ, hζ, hzeta⟩ := exists_zeta_uniform (n := n) hK hn ε k
    obtain ⟨-, hV⟩ := hform k ζ hζ (hzeta ς hς)
    rw [← hk, hV θ₀ hθ₀]
    refine Filter.Tendsto.congr' ?_ ((continuousOn_VPoly_exponent ζ _ _) θ₀ hθ₀).tendsto
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hV t ht).symm

/-- **`w ≤ U` for the regularised element**, at every character and every
`ς ≥ 0`. This is `Lyons.InvExtBlock.Ublock_ge_norm_Vblock` applied to the
family, its two hypotheses being
`Lyons.Converse.isPos_regTestElement` and
`Lyons.Converse.invol_regTestElement`. -/
private theorem wreg_le_Ureg {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) {ε : ℝ}
    (hε : 0 ≤ ε) {ς : ℝ} (hς : 0 ≤ ς) (k : ZMod n) :
    wreg (n := n) K ε k ς ≤ Ureg (n := n) K ε k ς :=
  InvExtBlock.Ublock_ge_norm_Vblock (chi k) (0 : ZMod n) _
    (isPos_regTestElement hK hn hε hς) (invol_regTestElement K ε ς)

/-- **The block data is bounded uniformly over `ς ∈ [0, 1]` and over characters.**

`Ureg` is continuous in `ς` (`continuous_Ureg`) and `[0, 1]` is compact, so each
of the finitely many `χ_k` admits a bound; the dual of `ZMod n` being finite, a
single `B` serves all of them. `wreg` needs no separate argument, being at most
`Ureg` by `wreg_le_Ureg`.

This is what makes the dominating constant independent of `ς`, and it is the
last ingredient of `hbound`. -/
private theorem exists_bound_blockData {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ς ∈ Set.Icc (0 : ℝ) 1, ∀ k : ZMod n,
      Ureg (n := n) K ε k ς ≤ B ∧ wreg (n := n) K ε k ς ≤ B := by
  -- One bound per character, on the compact interval.
  have hper : ∀ k : ZMod n, ∃ Bk : ℝ, ∀ ς ∈ Set.Icc (0 : ℝ) 1,
      Ureg (n := n) K ε k ς ≤ Bk := by
    intro k
    obtain ⟨Bk, hBk⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := Ureg (n := n) K ε k) (continuous_Ureg hK hn ε k).continuousOn
    exact ⟨Bk, fun ς hς => (le_abs_self _).trans
      ((Real.norm_eq_abs _).symm.trans_le (hBk ς hς))⟩
  choose Bfun hBfun using hper
  -- The dual is finite, so the finitely many bounds have a maximum.
  refine ⟨max 0 (Finset.univ.sup' Finset.univ_nonempty Bfun), le_max_left _ _,
    fun ς hς k => ?_⟩
  have hk : Bfun k ≤ Finset.univ.sup' Finset.univ_nonempty Bfun :=
    Finset.le_sup' Bfun (Finset.mem_univ k)
  have hU : Ureg (n := n) K ε k ς ≤ max 0 (Finset.univ.sup' Finset.univ_nonempty Bfun) :=
    (hBfun k ς hς).trans (hk.trans (le_max_right _ _))
  exact ⟨hU, (wreg_le_Ureg hK hn hε hς.1 k).trans hU⟩

/-- **Every coefficient of the regularised element is bounded by `B`.** -/
private theorem abs_co_regTestElement_le {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {B : ℝ} {ς : ℝ}
    (hς : ς ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ k : ZMod n, Ureg (n := n) K ε k ς ≤ B ∧ wreg (n := n) K ε k ς ≤ B)
    (g : InvExt (ZMod n) 0) : |co (regTestElement n K ε ς) g| ≤ B := by
  refine abs_co_le_of_blocks_le (0 : ZMod n) (fun ψ => ?_) (fun ψ => ?_) g
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    -- `Ublock` is real, so its norm is `|U|`, and `0 ≤ w ≤ U`.
    have hnn : 0 ≤ Ureg (n := n) K ε k ς :=
      le_trans (norm_nonneg _) (wreg_le_Ureg hK hn hε hς.1 k)
    rw [← hk, ← ofReal_Ureg K ε k ς, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnn]
    exact (hB k).1
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    rw [← hk]
    exact (hB k).2

/-- **Every coefficient of the sandwich is bounded by the same `B`.**

This is where `norm_UPoly_le` and `norm_VPoly_le` pay off: the abelian entry is
bounded by `w` and the outside entry by `U`, and both `U` and `w` are at most `B`,
so no separate constant is needed for the sandwich. -/
private theorem abs_co_sandwich_regTestElement_le {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {B : ℝ} {ς : ℝ}
    (hς : ς ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ k : ZMod n, Ureg (n := n) K ε k ς ≤ B ∧ wreg (n := n) K ε k ς ≤ B)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (g : InvExt (ZMod n) 0) :
    |co (sandwich (regTestElement n K ε ς)
      (InvExt.b : InvExt (ZMod n) 0) θ) g| ≤ B := by
  refine abs_co_le_of_blocks_le (0 : ZMod n) (fun ψ => ?_) (fun ψ => ?_) g
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    obtain ⟨ζ, hζ, hzeta⟩ := exists_zeta_uniform (n := n) hK hn ε k
    rw [← hk, Ublock_sandwich_reg hK hn hε hθ hθ' hς.1 k hζ (hzeta ς hς.1)]
    exact (norm_UPoly_le hζ (norm_nonneg _) (wreg_le_Ureg hK hn hε hς.1 k) hθ
      hθ').trans (hB k).2
  · obtain ⟨k, hk⟩ := (cyclicAddChar_bijective (ZMod.card n) exists_zsmul_one).2 ψ
    obtain ⟨ζ, hζ, hzeta⟩ := exists_zeta_uniform (n := n) hK hn ε k
    rw [← hk, Vblock_sandwich_reg hK hn hε hθ hθ' hς.1 k hζ (hzeta ς hς.1)]
    exact (norm_VPoly_le hζ (norm_nonneg _) (wreg_le_Ureg hK hn hε hς.1 k) hθ
      hθ').trans (hB k).1

/-- **The energy is continuous in the regularisation parameter.**

  `𝓔_p(ξ_{n,K,ε,ς}; τ) → 𝓔_p(ξ_{n,K,ε}; τ)` as `ς → 0⁺`.

Dominated convergence, `Lyons.tendsto_intervalIntegral_of_dominated`, with its
three hypotheses supplied by `tendsto_energyIntegrand` (`hlim`),
`continuousOn_co_sandwich_regTestElement` (`hmeas`), and the two coefficient
bounds above against `exists_bound_blockData` (`hbound`).

The hypotheses on `K` and `n` are `2 ≤ K` and `2 * K < n`, inherited from
`rhoAlg_regTestElement` as everywhere in this file. `p ≥ 1` **is** assumed and is
genuinely needed — see below. The nonvanishing hypothesis is on the *test*
element.

Dominated convergence is applied on `T = (0, 1]`; the conclusion is then stated
along `𝓝[>] 0`, the two filters agreeing because `Iic 1` is a neighbourhood of
`0`. That is what lets `exists_energy_regTestElement_pos` consume it through
`Lyons.exists_pos_of_tendsto_nhdsGT`.

## Where `p ≥ 1` is used, and where it is not

Only in `hbound`, and only through `|J_p(y)| ≤ |y|^{p-1}`
(`abs_signedPow_le_abs_rpow`): bounding `|y|^{p-1}` by `B^{p-1}` needs the
exponent nonnegative, since `Real.rpow_le_rpow` is monotone in the base only for
a nonnegative exponent. At `p < 1` the estimate runs the wrong way and a
coefficient near `0` would make `J_p` large, so the hypothesis is not decoration.

It is *not* needed for `hlim`, which instead needs the coefficients to be nonzero
— `continuousAt_signedPow` is continuity of `J_p` away from the origin and holds
for every real `p`. The two hypotheses are doing different jobs. -/
@[lyons_tag "lem_Ep_reg_limit"]
theorem tendsto_energy_regTestElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    {ε : ℝ} (hε : 0 ≤ ε) {p : ℝ} (hp : 1 ≤ p)
    (hne : ∀ g : InvExt (ZMod n) 0, co (testElement n K ε) g ≠ 0) :
    Filter.Tendsto
      (fun ς => energy p (regTestElement n K ε ς) (InvExt.b : InvExt (ZMod n) 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0))) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_blockData hK hn hε
  -- Near `0` the interval `(0,1]` generates the same filter as `(0,∞)`.
  have hfilter : nhdsWithin (0 : ℝ) (Set.Ioc 0 1) = nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← Set.Ioi_inter_Iic, Set.inter_comm]
    exact nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds one_pos))
  rw [← hfilter]
  simp only [energy_def]
  refine tendsto_intervalIntegral_of_dominated (a := 0) (b := 1) zero_le_one
    (C := (Fintype.card (InvExt (ZMod n) 0) : ℝ) * (B ^ (p - 1) * (B + B)))
    (fun ς hς => ?_) (fun ς hς => ?_) ?_
  · -- `hmeas`: the integrand is continuous on the open interval, and `Ioc`
    -- differs from `Ioo` by the null set `{1}`.
    have hmem : ς ∈ Set.Icc (0 : ℝ) 1 := ⟨hς.1.le, hς.2⟩
    have hcont : ContinuousOn (fun θ : ℝ => ∑ g : InvExt (ZMod n) 0,
        signedPow p (co (regTestElement n K ε ς) g)
          * (co (sandwich (regTestElement n K ε ς)
              (InvExt.b : InvExt (ZMod n) 0) θ) g
            - co (regTestElement n K ε ς) g)) (Set.Ioo 0 1) :=
      continuousOn_finsetSum _ fun g _ =>
        continuousOn_const.mul
          ((continuousOn_co_sandwich_regTestElement hK hn hε hς.1.le g).sub
            continuousOn_const)
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · -- `hbound`: termwise, `|J_p| ≤ B^{p-1}` and the difference is at most `2B`.
    have hmem : ς ∈ Set.Icc (0 : ℝ) 1 := ⟨hς.1.le, hς.2⟩
    refine Filter.Eventually.of_forall fun θ hθmem => ?_
    have hθ : (0 : ℝ) ≤ θ := hθmem.1.le
    have hθ' : θ ≤ 1 := hθmem.2.le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ g : InvExt (ZMod n) 0,
        |signedPow p (co (regTestElement n K ε ς) g)
            * (co (sandwich (regTestElement n K ε ς)
                (InvExt.b : InvExt (ZMod n) 0) θ) g
              - co (regTestElement n K ε ς) g)|
          ≤ B ^ (p - 1) * (B + B) := by
      intro g
      have hx := abs_co_regTestElement_le hK hn hε hmem (hB ς hmem) g
      have hs := abs_co_sandwich_regTestElement_le hK hn hε hmem (hB ς hmem) hθ hθ' g
      have hJ : |signedPow p (co (regTestElement n K ε ς) g)| ≤ B ^ (p - 1) :=
        (abs_signedPow_le_abs_rpow p _).trans
          (Real.rpow_le_rpow (abs_nonneg _) hx (by linarith))
      have hdiff : |co (sandwich (regTestElement n K ε ς)
          (InvExt.b : InvExt (ZMod n) 0) θ) g
            - co (regTestElement n K ε ς) g| ≤ B + B :=
        (abs_sub _ _).trans (add_le_add hs hx)
      rw [abs_mul]
      exact mul_le_mul hJ hdiff (abs_nonneg _)
        (Real.rpow_nonneg hB0 _)
    calc ∑ g : InvExt (ZMod n) 0,
            |signedPow p (co (regTestElement n K ε ς) g)
              * (co (sandwich (regTestElement n K ε ς)
                  (InvExt.b : InvExt (ZMod n) 0) θ) g
                - co (regTestElement n K ε ς) g)|
        ≤ ∑ _g : InvExt (ZMod n) 0, B ^ (p - 1) * (B + B) :=
          Finset.sum_le_sum fun g _ => hterm g
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · -- `hlim`: the pointwise convergence.
    refine Filter.Eventually.of_forall fun θ hθmem => ?_
    rw [hfilter]
    exact tendsto_energyIntegrand hK hn hε p hne hθmem.1.le hθmem.2.le

/-- **The energy stays positive after regularisation.** If
`𝓔_p(ξ_{n,K,ε}; τ) > 0` then there is `ς₀ > 0` with `𝓔_p(ξ_{n,K,ε,ς}; τ) > 0` for
every `0 < ς < ς₀`.

This is `Lyons.exists_pos_of_tendsto_nhdsGT` applied to
`tendsto_energy_regTestElement`; the `Θ/2` manoeuvre it packages is stated once
in `Lyons.Analysis.EventuallyPos`.

Hypotheses as in `tendsto_energy_regTestElement`, plus the positivity being
propagated. -/
@[lyons_tag "lem_Ep_reg_pos"]
theorem exists_energy_regTestElement_pos {K : ℤ} (hK : 2 ≤ K)
    (hn : 2 * K < (n : ℤ)) {ε : ℝ} (hε : 0 ≤ ε) {p : ℝ} (hp : 1 ≤ p)
    (hne : ∀ g : InvExt (ZMod n) 0, co (testElement n K ε) g ≠ 0)
    (hpos : 0 < energy p (testElement n K ε) (InvExt.b : InvExt (ZMod n) 0)) :
    ∃ ς₀ > 0, ∀ ς : ℝ, 0 < ς → ς < ς₀ →
      0 < energy p (regTestElement n K ε ς) (InvExt.b : InvExt (ZMod n) 0) :=
  exists_pos_of_tendsto_nhdsGT hpos (tendsto_energy_regTestElement hK hn hε hp hne)

end SideConditions

end Lyons.Converse
