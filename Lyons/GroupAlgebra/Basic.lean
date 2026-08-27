/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Lyons.Meta.Tag

/-!
# The real group algebra of a finite group, via its left regular representation

For a finite group `G` we work in `MonoidAlgebra ℝ G` and transport every
analytic question along the **left regular representation**

`L x : Matrix G G ℂ`,  `(L x) g h = x (g * h⁻¹)`.

`L` is an injective `ℝ`-algebra map that intertwines the involution with the
conjugate transpose, so positivity, fractional powers and the continuous
functional calculus can all be *imported* from `Matrix` rather than rebuilt on
`MonoidAlgebra`. That is the whole reason for routing through `L`: Mathlib
equips `Matrix` with a `ContinuousFunctionalCalculus` instance and does not
equip `MonoidAlgebra` with one, and the argument this file supports needs
`CFC.rpow` and `CFC.nnrpow_add`.

`MonoidAlgebra` supplies the ring structure, so associativity and
distributivity come for free. It does **not** carry a `StarRing` instance for a
group, so the involution is defined here.

## Main definitions

* `Lyons.invol` : the involution `x⋆ g = x g⁻¹` (real coefficients, so no
  conjugation).
* `Lyons.L` : the left regular representation as a complex matrix.
* `Lyons.IsPos` : `x ⪰ 0`, meaning `L x` is positive semidefinite.

## Main results

* `Lyons.L_mul`, `Lyons.L_invol`, `Lyons.L_injective` : `L` is a
  star-preserving injective ring map.
* `Lyons.L_add`, `Lyons.L_zero` : additivity.
-/

open Finset Matrix

-- `Matrix.PosSemidef` needs an order on the entries, and Complex's order is
-- deliberately scoped in Mathlib so it cannot be picked up by accident.
open scoped ComplexOrder

namespace Lyons

variable {G : Type*}

/-! ### Coefficients

`MonoidAlgebra ℝ G` is a structure wrapping `coeff : G →₀ ℝ`. `co x g` is the
coefficient of `x` at `g`; it exists to keep the statements below readable and
to isolate the one piece of `Finsupp` plumbing. -/

/-- The coefficient of `x` at `g`. -/
@[lyons_tag "not_coeff"]
def co (x : MonoidAlgebra ℝ G) (g : G) : ℝ := x.coeff g

@[simp] theorem co_add (x y : MonoidAlgebra ℝ G) (g : G) :
    co (x + y) g = co x g + co y g := rfl

@[simp] theorem co_zero (g : G) : co (0 : MonoidAlgebra ℝ G) g = 0 := rfl

theorem co_injective {x y : MonoidAlgebra ℝ G} (h : ∀ g, co x g = co y g) : x = y := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  simpa using Finsupp.ext h

/-- Rewrite a `Finsupp.sum` over the coefficients as a sum over all of `G`.
Every statement below is a sum over `univ`, and `MonoidAlgebra`'s `coeff_mul_*`
lemmas produce `Finsupp.sum`; this is the bridge. -/
theorem finsuppSum_eq_sum [Fintype G] (x : MonoidAlgebra ℝ G) (F : G → ℝ → ℝ)
    (hF : ∀ g, F g 0 = 0) : (x.coeff.sum F) = ∑ g : G, F g (co x g) :=
  Finsupp.sum_fintype _ _ hF

/-- **The convolution rule.** The algebra structure on `ℝ[G]` is Mathlib's
`MonoidAlgebra`, and this identity is what its multiplication amounts to on
coefficients; every coefficient computation below begins by invoking it. -/
@[lyons_tag "def_group_algebra"]
theorem co_mul [Group G] [Fintype G]
    (x y : MonoidAlgebra ℝ G) (g : G) :
    co (x * y) g = ∑ h : G, co x (g * h⁻¹) * co y h := by
  classical
  rw [co, MonoidAlgebra.coeff_mul_apply_right]
  exact finsuppSum_eq_sum _ _ fun _ ↦ mul_zero _

/-! ### Coefficient plumbing

`co` is additive by `rfl`; these extend that to the remaining algebra
operations, so coefficient computations become `simp` calls. -/

section Plumbing
variable {G : Type*} [Monoid G]

@[simp] theorem co_sub (x y : MonoidAlgebra ℝ G) (g : G) :
    co (x - y) g = co x g - co y g := rfl

@[simp] theorem co_smul (r : ℝ) (x : MonoidAlgebra ℝ G) (g : G) :
    co (r • x) g = r * co x g := rfl

omit [Monoid G] in
theorem co_sum {ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℝ G) (g : G) :
    co (∑ i ∈ s, f i) g = ∑ i ∈ s, co (f i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp [co]
  | insert a s ha ih => rw [Finset.sum_insert ha, co_add, ih, Finset.sum_insert ha]

section
variable [DecidableEq G]

@[simp] theorem co_one (g : G) :
    co (1 : MonoidAlgebra ℝ G) g = if g = 1 then 1 else 0 := by
  simp [co, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    eq_comm]

omit [Monoid G] in
@[simp] theorem co_single (s : G) (r : ℝ) (g : G) :
    co (MonoidAlgebra.single s r) g = if g = s then r else 0 := by
  simp [co, MonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

end

end Plumbing

/-- Expansion of an element over the basis of group elements. Used whenever a
statement about an algebra map has to be checked one basis element at a time.

Note when rewriting with this: the right-hand side mentions `co x g`, so
`rw [basis_expansion x]` will also rewrite inside those coefficients. Use
`conv_lhs` or freeze the coefficient function first. -/
theorem basis_expansion [Fintype G] (x : MonoidAlgebra ℝ G) :
    x = ∑ g : G, MonoidAlgebra.single g (co x g) := by
  classical
  refine co_injective fun h ↦ ?_
  rw [co_sum, Finset.sum_eq_single h]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hcon; exact absurd (Finset.mem_univ h) hcon

/-- Build an element from a coefficient function. Inverse to `co` on a finite
group; used to read a group-algebra element off a matrix column. -/
noncomputable def ofFun [Fintype G] (f : G → ℝ) : MonoidAlgebra ℝ G :=
  ∑ g : G, MonoidAlgebra.single g (f g)

@[simp] theorem co_ofFun [Fintype G] (f : G → ℝ) (g : G) :
    co (ofFun f) g = f g := by
  classical
  rw [ofFun, co_sum, Finset.sum_eq_single g]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hcon; exact absurd (Finset.mem_univ g) hcon

/-! ### The involution -/

/-- The involution `x⋆ g = x g⁻¹`. The coefficients are real, so unlike the
complex group algebra there is no conjugation. -/
@[lyons_tag "def_involution"]
def invol [Group G] (x : MonoidAlgebra ℝ G) : MonoidAlgebra ℝ G :=
  .ofCoeff (Finsupp.equivMapDomain (Equiv.inv G) x.coeff)

@[simp] theorem co_invol [Group G] (x : MonoidAlgebra ℝ G) (g : G) :
    co (invol x) g = co x g⁻¹ := by
  simp [co, invol, Finsupp.equivMapDomain_apply]

/-! ### The left regular representation -/

/-- The left regular representation, as a complex `G × G` matrix. -/
@[lyons_tag "def_left_regular"]
def L [Group G] (x : MonoidAlgebra ℝ G) : Matrix G G ℂ :=
  Matrix.of fun g h => ((co x (g * h⁻¹) : ℝ) : ℂ)

@[simp] theorem L_apply [Group G] (x : MonoidAlgebra ℝ G) (g h : G) :
    L x g h = ((co x (g * h⁻¹) : ℝ) : ℂ) := rfl

@[simp] theorem L_add [Group G] (x y : MonoidAlgebra ℝ G) : L (x + y) = L x + L y := by
  ext g h; simp [L_apply]

@[simp] theorem L_zero [Group G] : L (0 : MonoidAlgebra ℝ G) = 0 := by
  ext g h; simp [L_apply]

@[simp] theorem L_sub [Group G] (x y : MonoidAlgebra ℝ G) : L (x - y) = L x - L y := by
  ext g h; simp [L_apply]

@[simp] theorem L_smul [Group G] (r : ℝ) (x : MonoidAlgebra ℝ G) :
    L (r • x) = r • L x := by
  ext g h
  simp only [L_apply, co_smul, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]

@[simp] theorem L_one [Group G] [DecidableEq G] : L (1 : MonoidAlgebra ℝ G) = 1 := by
  ext g h
  by_cases hgh : g = h
  · subst hgh; simp [L_apply]
  · have hne : g * h⁻¹ ≠ 1 := fun hcon => hgh (mul_inv_eq_one.mp hcon)
    simp [L_apply, hgh, hne]

/-- `L` is multiplicative. -/
@[lyons_tag "lem_L_mul"]
theorem L_mul [Group G] [Fintype G] (x y : MonoidAlgebra ℝ G) :
    L (x * y) = L x * L y := by
  ext g h
  -- Left side: expand the convolution coefficient at `g * h⁻¹`.
  rw [L_apply, co_mul, Matrix.mul_apply]
  push_cast
  -- Right side: reindex the matrix sum by `u = k * h`.
  refine Fintype.sum_equiv (Equiv.mulRight h)
      (fun k : G => ((co x (g * h⁻¹ * k⁻¹) : ℝ) : ℂ) * ((co y k : ℝ) : ℂ))
      (fun u : G => ((co x (g * u⁻¹) : ℝ) : ℂ) * ((co y (u * h⁻¹) : ℝ) : ℂ))
      (fun k => ?_)
  have h1 : g * (k * h)⁻¹ = g * h⁻¹ * k⁻¹ := by group
  have h2 : k * h * h⁻¹ = k := by group
  simp only [Equiv.coe_mulRight, h1, h2]

/-- `L` intertwines the involution with the conjugate transpose. -/
@[lyons_tag "lem_L_star"]
theorem L_invol [Group G] (x : MonoidAlgebra ℝ G) : L (invol x) = (L x)ᴴ := by
  ext g h
  rw [L_apply, Matrix.conjTranspose_apply, L_apply, co_invol]
  rw [Complex.star_def, Complex.conj_ofReal]
  congr 1
  congr 1
  group

/-- `L` is injective: read the coefficients off the column at the identity. -/
@[lyons_tag "lem_L_injective"]
theorem L_injective [Group G] : Function.Injective (L (G := G)) := by
  intro x y hxy
  refine co_injective fun g => ?_
  have h := congrArg (fun M => M g 1) hxy
  simpa [L_apply] using h

/-- `L` bundled as an `ℝ`-algebra homomorphism.

The unbundled `L` is what every statement below uses, because its defining
equation `L_apply` is the workhorse. The bundled form exists for the one purpose
the unbundled form cannot serve: `Polynomial.aeval_algHom_apply`, which transfers
a polynomial evaluation along a map, is stated for bundled algebra maps only. -/
noncomputable def Lalg [Group G] [Fintype G] [DecidableEq G] :
    MonoidAlgebra ℝ G →ₐ[ℝ] Matrix G G ℂ where
  toFun := L
  map_one' := L_one
  map_mul' := L_mul
  map_zero' := L_zero
  map_add' := L_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, L_smul, L_one]

@[simp] theorem Lalg_apply [Group G] [Fintype G] [DecidableEq G]
    (x : MonoidAlgebra ℝ G) : Lalg x = L x := rfl

/-! ### Positivity -/

/-- `x ⪰ 0`, defined as positive semidefiniteness of `L x`. -/
@[lyons_tag "def_positive"]
def IsPos [Group G] [Fintype G] (x : MonoidAlgebra ℝ G) : Prop :=
  (L x).PosSemidef

theorem IsPos.isHermitian [Group G] [Fintype G] {x : MonoidAlgebra ℝ G}
    (hx : IsPos x) :
    (L x).IsHermitian := Matrix.PosSemidef.isHermitian hx

/-- A positive element is self-adjoint. This is where routing through `L` pays
off: Hermitianness of the matrix transports back along injectivity. -/
theorem IsPos.invol_eq [Group G] [Fintype G] {x : MonoidAlgebra ℝ G}
    (hx : IsPos x) : invol x = x :=
  L_injective (by rw [L_invol, IsPos.isHermitian hx])

end Lyons
