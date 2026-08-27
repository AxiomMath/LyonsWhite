/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Fourier.Parseval
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.ZMod.Basic

/-!
# The cyclic character dictionary

The Fourier layer of this development indexes transforms by the characters of a
finite abelian group (`Lyons.AddCharFourier.dft`, with `AddChar A ℂ` for
the dual group `Â`), while every exponential sum of the converse direction is
written in powers of `ω_n = e^{2πi/n}`.  This file is the translation.  Nothing
here mentions the inversion extension: it is a statement about a cyclic group
and its characters alone.

## Main definitions

* `Lyons.Converse.omegaN` : the root of unity `ω_n`.
* `Lyons.Converse.cyclicChar` : the character `χ_k`, whose value at `c^j` is
  `ω_n^{kj}`.

## Main results

* `Lyons.Converse.cyclicIndex_bijective` : `j ↦ c^j` is a bijection `ℤ/n → C`.
* `Lyons.Converse.cyclicChar_mem_range` : `χ_k ∈ Ĉ`.
* `Lyons.Converse.cyclicAddChar_bijective` : `k ↦ χ_k` is a bijection
  `ℤ/n → Ĉ`.
* `Lyons.Converse.sum_omegaN_pow` : `∑_{j} ω_n^{qj}` is `n` at `q = 0` and `0`
  otherwise.

## Implementation notes

`C` is written **additively**, as every abelian group in this development is, so
`c^j` is `j • c` and `Ĉ` is `AddChar C ℂ`.  A residue `j ∈ ℤ/n` is turned into a
natural number by `ZMod.val` before it is used as a multiplier or as an exponent
of `ω_n`; that this is independent of the lift is `zsmul_congr` below on the
group side, and is automatic on the exponent side because `omegaN_pow_val`
identifies `ω_n^{q.val}` with `ZMod.stdAddChar q`, which takes a residue as its
argument.

That identification is what carries the whole file.  Mathlib's
`ZMod.stdAddChar` is `j ↦ exp(2πi j/n)`, i.e. exactly `q ↦ ω_n^q` with the
exponent read in `ℤ/n`, and it is already known to be an `AddChar` and to be
injective.  So the two facts needed about `ω_n` — that
`ω_n^{k(j+j')} = ω_n^{kj}ω_n^{kj'}` and that `ω_n^k` determines `k` — are read
off it rather than proved by hand.

The characters appear in two shapes, because `Ĉ` is a type of bundled characters
here while `χ_k` is naturally a bare function `C → ℂ∖{0}`:

* `Lyons.Converse.cyclicChar` is the bare function, and
  `Lyons.Converse.cyclicChar_mem_range` is the assertion that it is the
  underlying function of some `AddChar C ℂ` — which is what "`χ_k ∈ Ĉ`" says
  once `Ĉ` is that type;
* `Lyons.Converse.cyclicAddChar` is the bundling, definitionally the same
  function (`cyclicAddChar_coe` is `rfl`), and the bijection
  `Lyons.Converse.cyclicAddChar_bijective` is stated about it because its
  codomain is `Ĉ`.

`Lyons.Converse.sum_omegaN_pow` is proved from the cyclic orthogonality relation
`ZMod.sum_stdAddChar_mul` rather than through the character bijection and general
character orthogonality: the `ZMod` form is already available and the dictionary
is not needed to reach it.
-/

namespace Lyons.Converse

open Finset

/-! ### The root of unity -/

/-- The root of unity `ω_n = e^{2πi/n}`. -/
@[lyons_tag "not_omega"]
noncomputable def omegaN (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / n)

/-- **The exponent may be read in `ℤ/n`.**  `ω_n^{q.val}` is Mathlib's standard
additive character at `q`, so `ω_n^m` depends only on the residue of `m` — and,
since `ZMod.stdAddChar` is an `AddChar`, this is also the source of every
multiplicativity fact about `ω_n` used below. -/
private theorem omegaN_pow_val {n : ℕ} [NeZero n] (q : ZMod n) :
    omegaN n ^ q.val = ZMod.stdAddChar q :=
  calc omegaN n ^ q.val
      = Complex.exp (2 * Real.pi * Complex.I * ((q.val : ℤ) : ℂ) / n) := by
        rw [omegaN, ← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ = ZMod.stdAddChar (((q.val : ℤ) : ZMod n)) := (ZMod.stdAddChar_coe _).symm
    _ = ZMod.stdAddChar q := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **Geometric sums of the root of unity.** -/
@[lyons_tag "lem_omega_sum"]
theorem sum_omegaN_pow (n : ℕ) [NeZero n] (q : ZMod n) :
    ∑ j : ZMod n, omegaN n ^ (q * j).val = if q = 0 then (n : ℂ) else 0 := by
  rw [Finset.sum_congr rfl fun j _ => omegaN_pow_val (q * j)]
  exact ZMod.sum_stdAddChar_mul q

/-! ### Indexing a cyclic group by its generator -/

variable {C : Type*} [AddCommGroup C] [Fintype C] {n : ℕ} {c : C}

/-- The order of the group annihilates every element, in the `ℤ`-action. -/
private theorem zsmul_card_eq_zero (hcard : Fintype.card C = n) (c : C) : (n : ℤ) • c = 0 := by
  rw [← hcard]
  rw [natCast_zsmul]
  exact card_nsmul_eq_zero

/-- `j • c` depends on the integer `j` only through its residue mod `n`, because
`n • c = 0`.  This is the well-definedness half of
`cyclicIndex_bijective`. -/
private theorem zsmul_congr (hcard : Fintype.card C = n) {a b : ℤ}
    (h : (a : ZMod n) = (b : ZMod n)) : a • c = b • c := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).mp h.symm
  have hab : a = b + (n : ℤ) * q := by linarith [hq]
  have hz : ((n : ℤ) * q) • c = 0 := by
    rw [mul_comm, mul_smul, zsmul_card_eq_zero hcard, smul_zero]
  rw [hab, add_zsmul, hz, add_zero]

/-- A cyclic group of order `n` has `n` elements, so `n ≠ 0`. -/
private theorem neZero_of_card (hcard : Fintype.card C = n) : NeZero n :=
  ⟨by rw [← hcard]; exact Fintype.card_ne_zero⟩

/-- **A generator indexes a cyclic group**: `j ↦ c^j` is a bijection from `ℤ/n`
onto `C`.  Written additively, so `c^j` is `j • c` with `j` lifted to a natural
number by `ZMod.val`. -/
@[lyons_tag "lem_cyclic_index"]
theorem cyclicIndex_bijective (hcard : Fintype.card C = n)
    (hgen : ∀ x : C, ∃ j : ℤ, j • c = x) :
    Function.Bijective (fun j : ZMod n => j.val • c) := by
  have _ : NeZero n := neZero_of_card hcard
  -- Surjective: reduce the integer exponent produced by `hgen` mod `n`.
  have hsurj : Function.Surjective (fun j : ZMod n => j.val • c) := by
    intro x
    obtain ⟨j, hj⟩ := hgen x
    refine ⟨(j : ZMod n), ?_⟩
    change ((j : ZMod n)).val • c = x
    rw [← hj, ← natCast_zsmul]
    exact zsmul_congr hcard (by rw [Int.cast_natCast, ZMod.natCast_zmod_val])
  -- Injective: `ℤ/n` and `C` are finite of the same cardinality.
  exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by rw [ZMod.card, hcard]⟩

/-- The indexing map of `cyclicIndex_bijective`, bundled as a homomorphism.  Its
underlying function is `cyclicIndexHom_apply`, i.e. `j ↦ c^j`;
the bundling is what lets the inverse be transported to characters. -/
private noncomputable def cyclicIndexHom (hcard : Fintype.card C = n) (c : C) : ZMod n →+ C :=
  ZMod.lift n ⟨zmultiplesHom C c, by rw [zmultiplesHom_apply]; exact zsmul_card_eq_zero hcard c⟩

private theorem cyclicIndexHom_intCast (hcard : Fintype.card C = n) (j : ℤ) :
    cyclicIndexHom hcard c (j : ZMod n) = j • c := by
  rw [cyclicIndexHom, ZMod.lift_coe, zmultiplesHom_apply]

private theorem cyclicIndexHom_apply [NeZero n] (hcard : Fintype.card C = n) (j : ZMod n) :
    cyclicIndexHom hcard c j = j.val • c := by
  have h : ((j.val : ℤ) : ZMod n) = j := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [← h]
  rw [cyclicIndexHom_intCast, natCast_zsmul]

private theorem cyclicIndexHom_one (hcard : Fintype.card C = n) :
    cyclicIndexHom hcard c 1 = c := by
  have h : ((1 : ℤ) : ZMod n) = 1 := by push_cast; rfl
  conv_lhs => rw [← h]
  rw [cyclicIndexHom_intCast, one_zsmul]

/-- The indexing bijection of `cyclicIndex_bijective` as an isomorphism
`ℤ/n ≃+ C`.
This is the object the character dictionary is built from: a character of `C` is
a character of `ℤ/n` read through it. -/
private noncomputable def cyclicIndexEquiv (hcard : Fintype.card C = n)
    (hgen : ∀ x : C, ∃ j : ℤ, j • c = x) : ZMod n ≃+ C :=
  have _ : NeZero n := neZero_of_card hcard
  AddEquiv.ofBijective (cyclicIndexHom hcard c) <| by
    have := cyclicIndex_bijective hcard hgen
    simpa [funext fun j : ZMod n => cyclicIndexHom_apply (c := c) hcard j] using this

private theorem cyclicIndexEquiv_symm_generator (hcard : Fintype.card C = n)
    (hgen : ∀ x : C, ∃ j : ℤ, j • c = x) : (cyclicIndexEquiv hcard hgen).symm c = 1 := by
  rw [AddEquiv.symm_apply_eq]
  exact (cyclicIndexHom_one hcard).symm

/-! ### The characters of a cyclic group -/

/-- **The cyclic characters** `χ_k : C → ℂ`, whose value at `c^j` is `ω_n^{kj}`.
The prescription is turned into a formula by inverting the indexing bijection
`cyclicIndex_bijective`, which is why the hypotheses naming `C` as cyclic of
order `n` with generator `c` appear as arguments. -/
@[lyons_tag "def_cyclic_char"]
noncomputable def cyclicChar (hcard : Fintype.card C = n)
    (hgen : ∀ x : C, ∃ j : ℤ, j • c = x) (k : ZMod n) : C → ℂ :=
  fun x => omegaN n ^ (k * (cyclicIndexEquiv hcard hgen).symm x).val

variable {hcard : Fintype.card C = n} {hgen : ∀ x : C, ∃ j : ℤ, j • c = x}

/-- The defining prescription of `cyclicChar`: the value of `χ_k` at `c^j` is
`ω_n^{kj}`. -/
theorem cyclicChar_apply_index (k j : ZMod n) :
    cyclicChar hcard hgen k (j.val • c) = omegaN n ^ (k * j).val := by
  have _ : NeZero n := neZero_of_card hcard
  rw [cyclicChar, show j.val • c = cyclicIndexEquiv hcard hgen j from
    (cyclicIndexHom_apply hcard j).symm, AddEquiv.symm_apply_apply]

/-- `χ_k` in terms of Mathlib's standard character of `ℤ/n`. -/
private theorem cyclicChar_eq_stdAddChar [NeZero n] (k : ZMod n) (x : C) :
    cyclicChar hcard hgen k x = ZMod.stdAddChar (k * (cyclicIndexEquiv hcard hgen).symm x) :=
  omegaN_pow_val _

/-- `χ_k`, bundled as an element of `Ĉ = AddChar C ℂ`.  Definitionally the
function `cyclicChar hcard hgen k`; the content is that the two `AddChar`
axioms hold for it. -/
noncomputable def cyclicAddChar (hcard : Fintype.card C = n)
    (hgen : ∀ x : C, ∃ j : ℤ, j • c = x) (k : ZMod n) : AddChar C ℂ where
  toFun := cyclicChar hcard hgen k
  map_zero_eq_one' := by
    have _ : NeZero n := neZero_of_card hcard
    rw [cyclicChar_eq_stdAddChar, map_zero, mul_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by
    have _ : NeZero n := neZero_of_card hcard
    rw [cyclicChar_eq_stdAddChar, cyclicChar_eq_stdAddChar, cyclicChar_eq_stdAddChar, map_add,
      mul_add, AddChar.map_add_eq_mul]

@[simp]
theorem cyclicAddChar_coe (k : ZMod n) :
    (cyclicAddChar hcard hgen k : C → ℂ) = cyclicChar hcard hgen k := rfl

/-- **The cyclic characters are characters**, `χ_k ∈ Ĉ`.  With `Ĉ` realized as
the type `AddChar C ℂ` of bundled characters, membership of the bare function
`χ_k` is the assertion that it is the underlying function of one of them. -/
@[lyons_tag "lem_cyclic_char_mem"]
theorem cyclicChar_mem_range (k : ZMod n) :
    cyclicChar hcard hgen k ∈ Set.range (fun ψ : AddChar C ℂ => (ψ : C → ℂ)) :=
  ⟨cyclicAddChar hcard hgen k, rfl⟩

/-- **The dictionary is a bijection**: `k ↦ χ_k` is a bijection from `ℤ/n` onto
`Ĉ`.

Injectivity is evaluation at `c`, where `χ_k` is `ω_n^k`, together with the
injectivity of `ZMod.stdAddChar` — Mathlib's packaging of the argument that
`e^{2πi(k-k')/n} = 1` forces `n ∣ k - k'`.  Surjectivity is then cardinality,
`|Ĉ| = |C| = n`, rather than a direct construction of a `k` from `χ(c)`. -/
@[lyons_tag "lem_cyclic_char_bij"]
theorem cyclicAddChar_bijective (hcard : Fintype.card C = n)
    (hgen : ∀ x : C, ∃ j : ℤ, j • c = x) :
    Function.Bijective (cyclicAddChar hcard hgen) := by
  have _ : NeZero n := neZero_of_card hcard
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun k k' hk => ?_, ?_⟩
  · have h := congrArg (fun ψ : AddChar C ℂ => ψ c) hk
    simp only [cyclicAddChar_coe] at h
    rw [cyclicChar_eq_stdAddChar, cyclicChar_eq_stdAddChar,
      cyclicIndexEquiv_symm_generator hcard hgen, mul_one, mul_one] at h
    exact ZMod.injective_stdAddChar h
  · rw [AddChar.card_eq, ZMod.card, hcard]

end Lyons.Converse
