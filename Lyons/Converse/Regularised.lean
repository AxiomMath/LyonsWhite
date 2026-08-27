/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Converse.Positive
import Lyons.Walk.Centered

/-!
# The regularised test element

The test element `ξ_{n,K,ε}` — `Lyons.Converse.testElement` — is positive but
not positive *definite* off the constants: some of its blocks vanish. Realising
the counterexample as a rate collection needs a strictly positive element, so a
multiple of `1 - π_G` is added,

  `ξ_{n,K,ε,ς} = ξ_{n,K,ε} + ς (1 - π_G)`,

where `π_G` is the uniform element. `1 - π_G` is the projection onto the
complement of the constants, so adding `ς` times it shifts every block *except*
the one at the trivial character, leaving `ξ π_G = 0` intact while making the
element positive definite off the constants for `ς > 0`.

## Main definitions

* `Lyons.Converse.regTestElement` : the regularised test element `ξ_{n,K,ε,ς}`.

## Main results

* `Lyons.Converse.invol_regTestElement` : `ξ_{n,K,ε,ς}` is self-adjoint.
* `Lyons.Converse.regTestElement_mul_uniform` : `ξ_{n,K,ε,ς} π_G = 0`.
* `Lyons.Converse.isPos_regTestElement` : `ξ_{n,K,ε,ς} ⪰ 0`.
* `Lyons.Converse.coeff_regTestElement_ne_zero` : no coefficient of
  `ξ_{n,K,ε,ς}` vanishes.
* `Lyons.Converse.isPosDefOffConst_regTestElement` : `ξ_{n,K,ε,ς}` is positive
  definite off the constants.

## Implementation notes

*The conventions are those of the test-element files.* As in
`Lyons.Converse.TestElement`, `Lyons.Converse.Blocks` and
`Lyons.Converse.Positive`, the cyclic group `C` of order `n` with generator
`c` is the **additively written** `ZMod n` with `c = 1`, so `z = 1` becomes
`z = 0` and `d = 1` becomes `d = 0`: the group is `Lyons.InvExt (ZMod n) 0`.
Since `C` is not a parameter but the concrete `ZMod n`, no hypothesis "`C` is
cyclic of order `n` with generator `c`" appears below.

*`K ≥ 2` suffices.* The two results that need hypotheses on `K` and `n` need
them only through `Lyons.Converse.testElement_mul_uniform` and
`Lyons.Converse.isPos_testElement`, for which `K ≥ 2` — the least that makes the
four residues `1`, `-1`, `K`, `-K` of `ℤ/n` pairwise distinct — is enough. The
condition `n > 2K` is written `2 * K < (n : ℤ)`.

*`ε ≥ 0` appears only where it is used.* It is genuinely needed only where
`Lyons.Converse.isPos_testElement` is, namely in `isPos_regTestElement` and
`isPosDefOffConst_regTestElement`; the other results do not assume it.
-/

namespace Lyons.Converse

open Lyons Matrix
open scoped ComplexOrder

variable {n : ℕ} [NeZero n]

/-- The **regularised test element** `ξ_{n,K,ε,ς} = ξ_{n,K,ε} + ς (1 - π_G)`.

As in `Lyons.Converse.testElement`, the cyclic group is `ZMod n` written
additively, so `z = 1` becomes `z = 0` here. No sign condition is placed on
`ς`. -/
@[lyons_tag "def_x_eps_reg"]
noncomputable def regTestElement (n : ℕ) [NeZero n] (K : ℤ) (ε ς : ℝ) :
    MonoidAlgebra ℝ (InvExt (ZMod n) 0) :=
  testElement n K ε + ς • (1 - uniform (InvExt (ZMod n) 0))

/-- The involution is additive. -/
private theorem invol_add' {G : Type*} [Group G] (x y : MonoidAlgebra ℝ G) :
    invol (x + y) = invol x + invol y :=
  co_injective fun g => by simp

/-- The involution commutes with real scalars. -/
private theorem invol_smul' {G : Type*} [Group G] (r : ℝ) (x : MonoidAlgebra ℝ G) :
    invol (r • x) = r • invol x :=
  co_injective fun g => by simp

/-- The involution fixes `1`, the neutral element being its own inverse. -/
private theorem invol_one' {G : Type*} [Group G] :
    invol (1 : MonoidAlgebra ℝ G) = 1 :=
  co_injective fun g => by classical simp [inv_eq_one]

/-- The involution is subtractive, from additivity. -/
private theorem invol_sub' {G : Type*} [Group G] (x y : MonoidAlgebra ℝ G) :
    invol (x - y) = invol x - invol y :=
  co_injective fun g => by simp

/-- **The regularised element is self-adjoint.**

The involution is additive and commutes with real scalars; it fixes `1` because
the neutral element is its own inverse, and it fixes `π_G` because the uniform
element has the same coefficient everywhere
(`Lyons.invol_uniform`). So it fixes `1 - π_G`, and it fixes `ξ_{n,K,ε}` by
`Lyons.Converse.invol_testElement`. -/
@[lyons_tag "lem_x_eps_reg_selfadjoint"]
theorem invol_regTestElement (K : ℤ) (ε ς : ℝ) :
    invol (regTestElement n K ε ς) = regTestElement n K ε ς := by
  rw [regTestElement, invol_add', invol_testElement, invol_smul', invol_sub',
    invol_one', invol_uniform]

/-! ### The regularised element annihilates the uniform element -/

/-- **The regularised element annihilates the uniform element**,
`ξ_{n,K,ε,ς} π_G = 0`.

Distributivity splits the product as `ξ_{n,K,ε} π_G + ς (π_G - π_G π_G)`; the
first term is `0` by `Lyons.Converse.testElement_mul_uniform` and the bracket is
`0` by `Lyons.uniform_idem`.

`hK` and `hn` are used only through `testElement_mul_uniform`, and `ε ≥ 0` is
not needed; see the module notes. -/
@[lyons_tag "lem_x_eps_reg_pi"]
theorem regTestElement_mul_uniform {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    (ε ς : ℝ) : regTestElement n K ε ς * uniform (InvExt (ZMod n) 0) = 0 := by
  rw [regTestElement, add_mul, testElement_mul_uniform hK hn, smul_mul_assoc,
    sub_mul, one_mul, uniform_idem, sub_self, smul_zero, add_zero]

/-! ### The complement of the constants

`1 - π_G` is the projection onto the complement of the constants. Both remaining
positivity results rest on the two facts collected here: it is an idempotent, and
it is a positive element. -/

section Complement

variable {G : Type*} [Group G] [Fintype G]

/-- `1 - π_G` is idempotent, `π_G` being idempotent by `Lyons.uniform_idem`. -/
private theorem one_sub_uniform_mul_self :
    (1 - uniform G) * (1 - uniform G) = 1 - uniform G := by
  classical
  have h : (1 - uniform G) * (1 - uniform G)
      = 1 - uniform G - uniform G + uniform G * uniform G := by noncomm_ring
  rw [h, uniform_idem]
  abel

/-- `1 - π_G ⪰ 0`.

On the matrix side this says that `P = L_{π_G}` is an orthogonal projection, so
`⟨(I - P)η, η⟩ = ‖(I - P)η‖² ≥ 0`. Inside the group algebra the same fact is one
line, because `1 - π_G` is a self-adjoint idempotent and hence equals
`(1 - π_G)⋆ (1 - π_G)`, to which `Lyons.isPos_invol_mul_self` applies. -/
private theorem isPos_one_sub_uniform : IsPos (1 - uniform G) := by
  classical
  have h : (1 - uniform G : MonoidAlgebra ℝ G) = invol (1 - uniform G) * (1 - uniform G) := by
    rw [invol_sub', invol_one', invol_uniform, one_sub_uniform_mul_self]
  rw [h]
  exact isPos_invol_mul_self _

variable [DecidableEq G]

/-- The matrix identity behind both positivity results:
`L_{ξ + ς(1 - π_G)} = L_ξ + ς (I - P)` with `P = L_{π_G}`, since `L` is additive,
`ℝ`-linear and unital. -/
private theorem L_add_smul_one_sub_uniform (x : MonoidAlgebra ℝ G) (ς : ℝ) :
    L (x + ς • (1 - uniform G)) = L x + ς • (1 - L (uniform G)) := by
  rw [L_add, L_smul, L_sub, L_one]

end Complement

/-! ### The regularised element is positive -/

/-- **The regularised element is positive**, `ξ_{n,K,ε,ς} ⪰ 0` for `ε ≥ 0` and
`ς ≥ 0`.

`L` is additive, so `L_{ξ_{n,K,ε,ς}} = L_{ξ_{n,K,ε}} + L_{ς(1 - π_G)}`; the
first summand is positive semidefinite by `Lyons.Converse.isPos_testElement` and
the second by `isPos_one_sub_uniform` together with `Lyons.IsPos.smul`, and a sum
of positive semidefinite matrices is positive semidefinite.

`hK` and `hn` are used only through `isPos_testElement`. -/
@[lyons_tag "lem_x_eps_reg_pos"]
theorem isPos_regTestElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ)) {ε ς : ℝ}
    (hε : 0 ≤ ε) (hς : 0 ≤ ς) : IsPos (regTestElement n K ε ς) := by
  rw [IsPos, regTestElement, L_add]
  -- `IsPos` unfolds to `(L ·).PosSemidef`, so `Lyons.IsPos.smul` must be named
  -- outright: dot notation on the hypothesis would find `Matrix.PosSemidef.smul`.
  exact (isPos_testElement hK hn hε).add (IsPos.smul isPos_one_sub_uniform hς)

/-! ### Coefficients of the regularised element -/

/-- The estimate behind `coeff_regTestElement_ne_zero`: a perturbation of size at
most `ς` cannot cancel a real number of absolute value more than `ς`. -/
private theorem add_mul_ne_zero_of_abs_le_one {y ς t : ℝ} (hς : 0 < ς) (ht : |t| ≤ 1)
    (h : ς < |y|) : y + ς * t ≠ 0 := by
  intro hzero
  have habs : |ς * t| < |y| :=
    calc |ς * t| = ς * |t| := by rw [abs_mul, abs_of_pos hς]
      _ ≤ ς := by nlinarith [abs_nonneg t]
      _ < |y| := h
  rw [show ς * t = -y by linarith, abs_neg] at habs
  exact absurd habs (lt_irrefl _)

/-- **Coefficients of the regularised element do not vanish.**

Addition and real scalar multiplication in `ℝ[G]` are coefficientwise, so
`(ξ_{n,K,ε,ς})_g = (ξ_{n,K,ε})_g + ς (1_g - (π_G)_g)` with `1_g ∈ {0, 1}` and
`(π_G)_g = 1/|G|`; both lie in `[0, 1]`, so the bracket has absolute value at
most `1` and the perturbation cannot cancel the leading coefficient.

**The hypothesis on `ς` is a pointwise one.** The natural condition is
`0 < ς < min_{g'} |(ξ_{n,K,ε})_{g'}|`, together with `(ξ_{n,K,ε})_{g'} ≠ 0` for
every `g'`. Since `G` is a nonempty finite type, that minimum exceeds `ς` exactly
when every `|(ξ_{n,K,ε})_{g'}|` does, which is `hςlt` below; and `hςlt` with `hς`
already forces every coefficient to be nonzero, so the nonvanishing condition is
redundant and is omitted. No `Finset` infimum is introduced, since none is needed
and the pointwise form is what `Lyons.Converse.coeff_testElement_ne_zero`
supplies at the call site.

**Only `|G| ≥ 1` is used.** Here `|G| = 2n`, so `(π_G)_g = 1/(2n)`, but only
`0 ≤ 1/|G| ≤ 1` matters: the proof below uses nothing about `G` beyond its being
a nonempty finite group.

`ε ≥ 0` is not needed; see the module notes. -/
@[lyons_tag "lem_x_eps_reg_coeff_ne_zero"]
theorem coeff_regTestElement_ne_zero (K : ℤ) {ε ς : ℝ} (hς : 0 < ς)
    (hςlt : ∀ g' : InvExt (ZMod n) 0, ς < |co (testElement n K ε) g'|)
    (g : InvExt (ZMod n) 0) : co (regTestElement n K ε ς) g ≠ 0 := by
  have hcard : (1 : ℝ) ≤ (Fintype.card (InvExt (ZMod n) 0) : ℝ) :=
    Nat.one_le_cast.mpr Fintype.card_pos
  have hinv0 : (0 : ℝ) ≤ ((Fintype.card (InvExt (ZMod n) 0) : ℝ))⁻¹ := by positivity
  have hinv1 : ((Fintype.card (InvExt (ZMod n) 0) : ℝ))⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hcard
  have habs : |(if g = 1 then (1 : ℝ) else 0)
      - ((Fintype.card (InvExt (ZMod n) 0) : ℝ))⁻¹| ≤ 1 := by
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  rw [regTestElement, co_add, co_smul, co_sub, co_one, coe_uniform]
  exact add_mul_ne_zero_of_abs_le_one hς habs (hςlt g)

/-! ### The regularised element is positive definite off the constants -/

/-- **The regularised element is positive definite off the constants.**

This is the point of the regularisation: `ξ_{n,K,ε}` alone is only semidefinite,
some of its blocks vanishing. With `P = L_{π_G}` and `η ≠ 0` killed by `P`,
`L_add_smul_one_sub_uniform` gives
`⟨L_{ξ_{n,K,ε,ς}} η, η⟩ = ⟨L_{ξ_{n,K,ε}} η, η⟩ + ς ⟨(I - P)η, η⟩`. The first term
is nonnegative by `Lyons.Converse.isPos_testElement`; in the second, `Pη = 0`
gives `(I - P)η = η`, so it is `ς ‖η‖² > 0`.

The conclusion is `Lyons.IsPosDefOffConst`, whose quadratic form is Mathlib's
`star η ⬝ᵥ (L x *ᵥ η)` in the scoped order on `ℂ`.

`hK` and `hn` are used only through `isPos_testElement`. -/
@[lyons_tag "lem_x_eps_reg_posdef"]
theorem isPosDefOffConst_regTestElement {K : ℤ} (hK : 2 ≤ K) (hn : 2 * K < (n : ℤ))
    {ε ς : ℝ} (hε : 0 ≤ ε) (hς : 0 < ς) :
    IsPosDefOffConst (regTestElement n K ε ς) := by
  intro η hη hPη
  have hvec : (ς • (1 - L (uniform (InvExt (ZMod n) 0)))) *ᵥ η = ς • η := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hPη, sub_zero]
  rw [regTestElement, L_add_smul_one_sub_uniform, Matrix.add_mulVec, dotProduct_add,
    hvec, dotProduct_smul, Complex.real_smul]
  refine add_pos_of_nonneg_of_pos
    ((isPos_testElement hK hn hε).dotProduct_mulVec_nonneg η) ?_
  exact mul_pos (by exact_mod_cast hς) (Matrix.dotProduct_star_self_pos_iff.mpr hη)

end Lyons.Converse
