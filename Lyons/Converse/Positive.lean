/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Blocks
import Lyons.GroupAlgebra.Positivity
import Lyons.InversionExtension.CoeffSplit
import Lyons.InversionExtension.Injective
import Lyons.Walk.Laplacian

/-!
# The test element is positive, and annihilates the uniform element

Three facts about `ξ_{n,K,ε}` read off its Fourier data, in the order they
depend on each other: the family is closed under squaring up to a factor of
two, hence every `ξ_{n,K,ε}` with `ε ≥ 0` is a positive element, and every one
of them kills the uniform element `π_G`.

## Main results

* `Lyons.Converse.testElement_mul_self` : `ξ_{n,K,ε} ξ_{n,K,ε} = 2 ξ_{n,K,ε²}`.
* `Lyons.Converse.isPos_testElement` : `ξ_{n,K,ε} ⪰ 0` for `ε ≥ 0`.
* `Lyons.Converse.testElement_mul_uniform` : `ξ_{n,K,ε} π_G = 0`.

## Implementation notes

*The conventions are those of the test-element files.*  As in
`Lyons.Converse.TestElement` and `Lyons.Converse.Blocks`, the cyclic
group `C` of order `n` with generator `c` is the **additively written** `ZMod n`
with `c = 1`, so `z = 1` becomes `z = 0` and `d = 1` becomes `d = 0`: the group
is `Lyons.InvExt (ZMod n) 0` and `ρ_{χ_k,1}` is
`InvExtBlock.rhoAlg (cyclicAddChar (ZMod.card n) exists_zsmul_one k) 0`.

*The scalar `2` is the real module action.*  `MonoidAlgebra ℝ G` is an
`ℝ`-algebra, so `2 ξ` could be read either as the module action `(2 : ℝ) • ξ` or
as the ring product `(2 : MonoidAlgebra ℝ G) * ξ`.  The statements below use
**`(2 : ℝ) • ξ`**, and correspondingly `(1/2 : ℝ) • ·` in the proof of
positivity.  The two readings agree, but the module action is the shape
`Lyons.IsPos.smul` consumes and the shape `InvExtBlock.rhoAlg` transports by
`map_smul`, so choosing it removes two rewrites and keeps the scalar out of the
group algebra's multiplication.

*`K ≥ 2` suffices.*  The hypotheses are exactly those of
`Lyons.Converse.rhoAlg_testElement`, and `K ≥ 2` is the least that makes the four
residues `1`, `-1`, `K`, `-K` of `ℤ/n` pairwise distinct.  Nothing here needs
more.

*`ε ≥ 0` appears only where it is used.*  It is a genuine hypothesis of
`isPos_testElement`, which takes a square root of `ε`, and of neither of the
other two results.
-/

namespace Lyons.Converse

open Finset Matrix

variable {n : ℕ} [NeZero n]

/-! ### The two `2 × 2` identities

The proof of `testElement_mul_self` is a case check on the four blocks of
`Lyons.Converse.rhoAlg_testElement`; three of the four cases are these two
lemmas, and the fourth is `0 * 0 = 2 • 0`. -/

-- Both entrywise checks finish a `simp` normal form with `ring1`/`norm_num`, which
-- is what the flexible linter flags; the normal form is not worth naming, since
-- the only content is the four scalar identities.
set_option linter.flexible false in
/-- `!![1,1;1,1]² = 2 !![1,1;1,1]`, the block identity at `k ∈ {1, -1}`. -/
private theorem ones_sq :
    (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1]
      = (2 : ℝ) • !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;> norm_num

set_option linter.flexible false in
/-- `(ε !![1,w;w',1])² = 2 (ε² !![1,w;w',1])` whenever `w w' = 1`, the block
identity at `k = K` and at `k = -K`.

The two cases needed are `w = i`, `w' = -i` and `w = -i`, `w' = i`, and both are
instances of the single hypothesis `w w' = 1`: the computation at `k = -K` is the
same as the one at `k = K` with `i` replaced by `-i` throughout, and
`i · (-i) = 1` is the only property of `i` it uses.  Taking `w` and `w'` as two
independent parameters rather than writing the second as `-w` keeps the statement
in the shape
`Lyons.Converse.rhoAlg_testElement` produces its `k = -K` matrix in, namely
`!![1, -i; i, 1]` rather than `!![1, -i; -(-i), 1]`. -/
private theorem twist_sq (ε : ℝ) {w w' : ℂ} (hw : w * w' = 1) :
    (ε • !![1, w; w', 1] : Matrix (Fin 2) (Fin 2) ℂ) * (ε • !![1, w; w', 1])
      = (2 : ℝ) • ((ε ^ 2 : ℝ) • !![1, w; w', 1]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;>
    first
      | ring1
      | linear_combination (ε : ℂ) ^ 2 * hw

/-! ### The test element is a square up to a factor -/

/-- **The test element is a square up to a factor**,
`ξ_{n,K,ε} ξ_{n,K,ε} = 2 ξ_{n,K,ε²}`.

The factor `2` is the real module action `(2 : ℝ) • ·`; see the module notes.

`Lyons.InvExtBlock.rhoAlg_injective` at `d = 0` reduces the identity to an
identity of blocks at every character of `ZMod n`, and
`Lyons.Converse.cyclicAddChar_bijective` says every character is `χ_k` for some
`k`.  Since `Lyons.InvExtBlock.rhoAlg` is an `ℝ`-algebra homomorphism, the block
of the product is the product of the blocks and the block of `2 • ξ` is `2 •` the
block, so `Lyons.Converse.rhoAlg_testElement` turns the goal into the four
displayed matrix identities.  The case distinctions of
`rhoAlg_testElement` depend only on `k`, `K` and `n` and not on the parameter
`ε`, which is what lets a single `split_ifs` line up the two sides.

`hK` and `hn` are used only through `rhoAlg_testElement`. -/
@[lyons_tag "lem_x_eps_sq"]
theorem testElement_mul_self {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε : ℝ) :
    testElement n K ε * testElement n K ε = (2 : ℝ) • testElement n K (ε ^ 2) := by
  refine InvExtBlock.rhoAlg_injective (0 : ZMod n) fun χ ↦ ?_
  obtain ⟨k, rfl⟩ :=
    (cyclicAddChar_bijective (ZMod.card n) (exists_zsmul_one (n := n))).surjective χ
  rw [map_mul, map_smul, rhoAlg_testElement hK hn, rhoAlg_testElement hK hn]
  split_ifs
  · exact ones_sq
  · exact twist_sq ε (by simp)
  · exact twist_sq ε (by simp)
  · simp

/-! ### The test element is positive -/

/-- **The test element is positive**, `ξ_{n,K,ε} ⪰ 0` for `ε ≥ 0`.

With `ε' = √ε`, so that `ε'² = ε`, `testElement_mul_self` gives
`ξ_{n,K,ε'} ξ_{n,K,ε'} = 2 ξ_{n,K,ε}`, hence
`ξ_{n,K,ε} = ½ ξ_{n,K,ε'} ξ_{n,K,ε'} = ½ (ξ_{n,K,ε'})^* ξ_{n,K,ε'}` by
`Lyons.Converse.invol_testElement`.  `Lyons.isPos_invol_mul_self` makes the
product positive and `Lyons.IsPos.smul` applies the nonnegative scalar `1/2`.

**A remark on the route.**  Positivity can also be read off the positive
semidefiniteness of the four nonzero blocks, but that needs the converse of the
statement that the blocks of a positive element are positive semidefinite — that
an element all of whose blocks are positive semidefinite is itself positive.
That converse is true, the direct sum of the `ρ_{χ,d}` being equivalent to the
left regular representation, but proving it costs an explicit intertwiner.  The
square above avoids it entirely, because the family of test elements happens to
be closed under squaring.

`hK` and `hn` are used only through `testElement_mul_self`. -/
@[lyons_tag "lem_x_eps_pos"]
theorem isPos_testElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) {ε : ℝ}
    (hε : 0 ≤ ε) : IsPos (testElement n K ε) := by
  have hsq := testElement_mul_self hK hn (Real.sqrt ε)
  rw [Real.sq_sqrt hε] at hsq
  have h : testElement n K ε
      = (1 / 2 : ℝ) •
        (invol (testElement n K (Real.sqrt ε)) * testElement n K (Real.sqrt ε)) := by
    rw [invol_testElement, hsq, smul_smul]
    norm_num
  rw [h]
  -- `IsPos` unfolds to `(L ·).PosSemidef`, so dot notation on the hypothesis
  -- would find `Matrix.PosSemidef.smul` instead; `Lyons.IsPos.smul` is named
  -- outright.
  exact IsPos.smul (isPos_invol_mul_self _) (by norm_num)

/-! ### The test element annihilates the uniform element -/

/-- The trivial character `χ_0` is identically `1`.  This is
`Lyons.Converse.cyclicChar` at `k = 0`, where the exponent `k j` of `ω_n`
vanishes for every `j`. -/
private theorem cyclicAddChar_zero_apply (x : ZMod n) :
    cyclicAddChar (ZMod.card n) (exists_zsmul_one (n := n)) (0 : ZMod n) x = 1 := by
  simp [cyclicAddChar, cyclicChar]

/-- **The test element annihilates the uniform element**, `ξ_{n,K,ε} π_G = 0`.

`Lyons.uniform_absorb` turns the product into `σ • π_G` with
`σ = ∑_{g ∈ G} ξ_g`, so it suffices that `σ = 0`.  `Lyons.sum_invExt` — the
reindexing underlying `Lyons.sum_coeff_split`, used at `d = 0` — splits `σ` into
an abelian and an outside half.  Because `χ_0` is identically `1`
(`cyclicAddChar_zero_apply`), those two halves are exactly the values at `χ_0`
of the two transforms `U^ξ` and `V^{ξ,0}` of
`Lyons.InvExtBlock.Ublock` and `Lyons.InvExtBlock.Vblock`, up to the coercion
`ℝ → ℂ`.

Both transforms vanish because the block at `χ_0` is the **zero** matrix: by
`Lyons.Converse.rhoAlg_testElement` that is the "otherwise" case, and
`Lyons.InvExtBlock.rhoAlg_entries` exhibits
`U^ξ(χ_0)` and `conj (V^{ξ,0}(χ_0))` as its `(0,0)` and `(1,0)` entries.

**Where the hypotheses are used.**  `hK` and `hn` are what put `0` outside
`{1, -1, K, -K}`, which is the whole content of the reduction: it is enough that
`1` and `K` are nonzero residues, and each is an integer strictly between `0`
and `n` precisely because `2 ≤ K` and `2K < n`.  `ε ≥ 0` is not needed. -/
@[lyons_tag "lem_x_eps_pi"]
theorem testElement_mul_uniform {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) (ε : ℝ) :
    testElement n K ε * uniform (InvExt (ZMod n) 0) = 0 := by
  -- `0 ∉ {1, -1, K, -K}` in `ℤ/n`.
  have hcast : ∀ m : ℤ, 0 < m → m < (n : ℤ) → ((m : ZMod n)) ≠ 0 := by
    intro m h0 hm
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hdvd => absurd (Int.le_of_dvd h0 hdvd) (by omega)
  have c1 : (1 : ZMod n) ≠ 0 := by
    have h := hcast 1 (by norm_num) (by omega)
    push_cast at h
    exact h
  have cK : ((K : ZMod n)) ≠ 0 := hcast K (by omega) (by omega)
  -- The block at `χ_0` is therefore the zero matrix.
  have hb := rhoAlg_testElement hK hn ε (0 : ZMod n)
  have c1' : ¬((0 : ZMod n) = 1 ∨ (0 : ZMod n) = -1) := by
    rintro (h | h)
    · exact c1 h.symm
    · exact c1 (by linear_combination h)
  rw [if_neg c1', if_neg (fun h => cK h.symm),
    if_neg (fun h => cK (by linear_combination h))] at hb
  -- Its `(0,0)` and `(1,0)` entries are the two transforms.
  have h00 : InvExtBlock.Ublock (testElement n K ε)
      (cyclicAddChar (ZMod.card n) (exists_zsmul_one (n := n)) (0 : ZMod n)) = 0 := by
    have hent := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hb
    simpa [InvExtBlock.rhoAlg_entries, InvExtBlock.Ublock] using hent
  have h10 : InvExtBlock.Vblock (testElement n K ε) 0
      (cyclicAddChar (ZMod.card n) (exists_zsmul_one (n := n)) (0 : ZMod n)) = 0 := by
    have hent := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hb
    simpa [InvExtBlock.rhoAlg_entries, InvExtBlock.Vblock] using hent
  -- At `χ_0` each transform is the plain coefficient sum of its half.
  have hU : ∑ a : ZMod n, co (testElement n K ε) (.rot a) = 0 := by
    have h : ((∑ a : ZMod n, co (testElement n K ε) (.rot a) : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum, ← h00, InvExtBlock.Ublock, AddCharFourier.dft_apply]
      exact Finset.sum_congr rfl fun a _ =>
        by rw [cyclicAddChar_zero_apply, mul_one, InvExtBlock.uCoeff]
    exact_mod_cast h
  have hV : ∑ a : ZMod n, co (testElement n K ε) (.refl (a + 0)) = 0 := by
    have h : ((∑ a : ZMod n, co (testElement n K ε) (.refl (a + 0)) : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum, ← h10, InvExtBlock.Vblock, AddCharFourier.dft_apply]
      exact Finset.sum_congr rfl fun a _ =>
        by rw [cyclicAddChar_zero_apply, mul_one, InvExtBlock.vCoeff]
    exact_mod_cast h
  rw [uniform_absorb, sum_invExt (0 : ZMod n) fun g => co (testElement n K ε) g, hU, hV,
    add_zero, zero_smul]

end Lyons.Converse
