/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.Abel

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

open Finset

namespace Lyons

variable {G : Type*}

/-- The coefficient of `x` at `g`. -/
def co (x : MonoidAlgebra ℝ G) (g : G) : ℝ := x.coeff g

/-- The left regular representation, as a complex `G × G` matrix. -/
def L [Group G] (x : MonoidAlgebra ℝ G) : Matrix G G ℂ :=
  Matrix.of fun g h => ((co x (g * h⁻¹) : ℝ) : ℂ)

/-- A **symmetric rate function**: nonnegative, invariant under inversion, and
vanishing at the identity.

Rates live on all of `G`, with value `0` at the identity rather than on
`G \ {1}`: the identity contributes `λ₁ • (1 - 1) = 0` to the Laplacian below, so
extending a rate by zero at `1` changes nothing it feeds. -/
structure RateFn (G : Type*) [Group G] where
  /-- The rate assigned to each group element. -/
  toFun : G → ℝ
  /-- Rates are nonnegative. -/
  nonneg' : ∀ g, 0 ≤ toFun g
  /-- Rates are symmetric under inversion. -/
  symm' : ∀ g, toFun g⁻¹ = toFun g
  /-- The identity carries no rate. -/
  atOne : toFun 1 = 0

namespace RateFn

variable {G : Type*} [Group G]

instance : FunLike (RateFn G) G ℝ where
  coe := RateFn.toFun
  coe_injective f g h := by cases f; cases g; congr

end RateFn

/-- The **group-algebra Laplacian** `Δ_λ = ∑ s, λ s • (1 - s)`. -/
noncomputable def laplacian [Group G] [Fintype G] (lam : RateFn G) :
    MonoidAlgebra ℝ G :=
  ∑ s : G, lam s • (1 - MonoidAlgebra.single s (1 : ℝ))

/-- The heat semigroup as a matrix: `exp (-t Δ_λ)` acting by left convolution. -/
noncomputable def heatMat [Group G] [Fintype G] [DecidableEq G] (lam : RateFn G)
    (t : ℝ) : Matrix G G ℂ :=
  NormedSpace.exp (-(t : ℂ) • L (laplacian lam))

/-- The **transition function** `p_t^λ`, the first column of `exp (-t Δ_λ)`. -/
noncomputable def heatCoeff [Group G] [Fintype G] [DecidableEq G]
    (lam : RateFn G) (t : ℝ) : G → ℂ :=
  fun g => heatMat lam t g 1

/-- The transition function `p_t^λ`, as an honestly `ℝ`-valued function. -/
noncomputable def heatCoeffReal [Group G] [Fintype G] [DecidableEq G]
    (lam : RateFn G) (t : ℝ) : G → ℝ :=
  fun g => (heatCoeff lam t g).re

/-- A **symmetric rate collection**: nonnegative and invariant under inversion,
with no condition at the identity. This is the paper's `λ ∈ ℝ_{≥0}^G` with
`λ_s = λ_{s⁻¹}`. -/
structure IsSymmRate [Group G] (lam : G → ℝ) : Prop where
  /-- Rates are nonnegative. -/
  nonneg : ∀ g, 0 ≤ lam g
  /-- Rates are symmetric under inversion. -/
  symm : ∀ g, lam g⁻¹ = lam g

/-- Discard the identity rate, which the walk ignores, to land in `RateFn`. -/
def IsSymmRate.toRateFn [Group G] [DecidableEq G] {lam : G → ℝ}
    (h : IsSymmRate lam) : RateFn G where
  toFun g := if g = 1 then 0 else lam g
  nonneg' g := by
    split
    · exact le_rfl
    · exact h.nonneg g
  symm' g := by
    by_cases hg : g = 1
    · simp [hg]
    · rw [if_neg (by simpa using hg), if_neg hg, h.symm g]
  atOne := by simp

/-- A rate collection is **generating** when its support generates `G`. -/
def Generating [Group G] (lam : G → ℝ) : Prop :=
  Subgroup.closure {s : G | 0 < lam s} = ⊤

/-- The **`ℓ^p` distance to stationarity**, the paper's `d_p^λ(t)`: the `ℓ^p`
distance between the walk's time-`t` distribution and the uniform distribution. -/
noncomputable def distToUniform [Group G] [Fintype G] [DecidableEq G] (p : ℝ)
    (lam : RateFn G) (t : ℝ) : ℝ :=
  (∑ g : G, |heatCoeffReal lam t g - (Fintype.card G : ℝ)⁻¹| ^ p) ^ p⁻¹

/-- **Rate-monotonicity.** The pair `(G, p)` is rate-monotonic when raising every
rate cannot increase the `ℓ^p` distance to stationarity, at any fixed time. -/
def RateMonotonic (G : Type*) [Group G] [Fintype G] [DecidableEq G] (p : ℝ) :
    Prop :=
  ∀ (lam mu : G → ℝ) (hlam : IsSymmRate lam) (hmu : IsSymmRate mu),
    Generating lam → Generating mu → (∀ s, lam s ≤ mu s) →
      ∀ t : ℝ, 0 ≤ t →
        distToUniform p hmu.toRateFn t ≤ distToUniform p hlam.toRateFn t

end Lyons

section InversionExtension

variable {A : Type*}

/-- The **inversion extension** of an abelian group `A` by an element `z`.
`rot a` is the element `a ∈ A`; `refl a` is `a * b`, where `b` is the adjoined
involution with `b a b⁻¹ = a⁻¹` and `b² = z`. -/
inductive InvExt (A : Type*) (z : A)
  /-- The element `a` of the abelian subgroup. -/
  | rot : A → InvExt A z
  /-- The element `a * b`, outside the abelian subgroup. -/
  | refl : A → InvExt A z
  deriving DecidableEq

namespace InvExt

section Defs

variable [AddCommGroup A] {z : A}

/-- Multiplication, read off the presentation: `b a = a⁻¹ b` and `b² = z`. -/
def mulTable : InvExt A z → InvExt A z → InvExt A z
  | rot a, rot a' => rot (a + a')
  | rot a, refl a' => refl (a + a')
  | refl a, rot a' => refl (a - a')
  | refl a, refl a' => rot (a - a' + z)

instance : Mul (InvExt A z) := ⟨mulTable⟩

instance : One (InvExt A z) := ⟨rot 0⟩

/-- Inversion: `(a)⁻¹ = -a` and `(a * b)⁻¹ = z * a * b`. -/
def invMap : InvExt A z → InvExt A z
  | rot a => rot (-a)
  | refl a => refl (a + z)

instance : Inv (InvExt A z) := ⟨invMap⟩

end Defs

section Group

variable [AddCommGroup A] {z : A} [hz : Fact (z + z = 0)]

/-- The group structure on `G_{A,z}`. `z + z = 0` is needed for **associativity**,
not merely for the presentation: with `refl` thrice, `refl a * (refl a' * refl a'')`
reduces to `refl (a - a' + a'' - z)` and `(refl a * refl a') * refl a''` to
`refl (a - a' + a'' + z)`, which agree precisely when `z = -z`. -/
instance : Group (InvExt A z) where
  mul_assoc x y w := by
    have hz' : -z = (z : A) := neg_eq_of_add_eq_zero_left hz.out
    cases x with
    | rot a =>
      cases y with
      | rot a' =>
        cases w with
        | rot a'' => exact congrArg rot (by abel)
        | refl a'' => exact congrArg refl (by abel)
      | refl a' =>
        cases w with
        | rot a'' => exact congrArg refl (by abel)
        | refl a'' => exact congrArg rot (by abel)
    | refl a =>
      cases y with
      | rot a' =>
        cases w with
        | rot a'' => exact congrArg refl (by abel)
        | refl a'' => exact congrArg rot (by abel)
      | refl a' =>
        cases w with
        | rot a'' => exact congrArg rot (by abel)
        | refl a'' =>
          refine congrArg refl ?_
          rw [show a - (a' - a'' + z) = a - a' + a'' + -z from by abel, hz']
          abel
  one_mul x := by
    cases x with
    | rot a => exact congrArg rot (zero_add a)
    | refl a => exact congrArg refl (zero_add a)
  mul_one x := by
    cases x with
    | rot a => exact congrArg rot (add_zero a)
    | refl a => exact congrArg refl (sub_zero a)
  inv_mul_cancel x := by
    cases x with
    | rot a => exact congrArg rot (neg_add_cancel a)
    | refl a =>
      refine congrArg rot ?_
      rw [show a + z - a + z = z + z from by abel]
      exact hz.out

end Group

section Card

variable {z : A}

/-- **Normal form.** Every element of `G_{A,z}` is uniquely `a` or `a * b`, so
the carrier is `A ⊕ A`. -/
def sumEquiv : A ⊕ A ≃ InvExt A z where
  toFun x := Sum.elim rot refl x
  invFun x := match x with | rot a => Sum.inl a | refl a => Sum.inr a
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance [Fintype A] : Fintype (InvExt A z) := Fintype.ofEquiv (A ⊕ A) sumEquiv

end Card

end InvExt

end InversionExtension

namespace Challenge

open Lyons

/-! ## The three objectives -/

/-- **`thm_main_forward` — Theorem A.** For all positive integers `n` and `m`,
raising every rate cannot increase the `ℓ^{2m}` distance of the dihedral walk's
time-`t` distribution from uniform. `NeZero n` is the paper's `n ≥ 1`, and is
what makes `DihedralGroup n` finite. -/
theorem thm_main_forward (n : ℕ) [NeZero n] (m : ℕ) (hm : 1 ≤ m) :
    RateMonotonic (DihedralGroup n) (2 * (m : ℝ)) :=
  sorry

/-- **`thm_main_general` — Theorem B.** The same holds over every inversion
extension of a finite abelian group by an involution — a family including the
generalized dihedral, dicyclic and generalized quaternion groups. `Fact (z+z=0)`
says `z` is an involution, the identity admitted, so Theorem A is `z = 0`. -/
theorem thm_main_general {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (z : A) [Fact (z + z = 0)] (m : ℕ) (hm : 1 ≤ m) :
    RateMonotonic (InvExt A z) (2 * (m : ℝ)) :=
  sorry

/-- **`thm_main_converse` — Theorem C.** For every real `p > 1` that is not an
even integer, there is an `n` for which the pair `(D_n, p)` is not
rate-monotonic.

The hypothesis is `1 < p`, not `1 ≤ p`: the case `p = 1`, the `ℓ¹` metric, is not
claimed here. -/
theorem thm_main_converse (p : ℝ) (hp : 1 < p)
    (hp2 : ∀ m : ℕ, 0 < m → p ≠ 2 * (m : ℝ)) :
    ∃ n : ℕ, ∃ _ : NeZero n, ¬ RateMonotonic (DihedralGroup n) p :=
  sorry

end Challenge
