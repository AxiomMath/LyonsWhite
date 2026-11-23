/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Tactic.Abel
public import Lyons.Definitions
public import Lyons.Meta.Tag

/-!
# The inversion extension `G_{A,z}`

For a finite abelian group `A` (written additively) and an element `z` with
`2 • z = 0`, the source's inversion extension is

  `G_{A,z} = ⟨A, b | b² = z, b a b⁻¹ = a⁻¹ for every a ∈ A⟩`,

every element of which is uniquely `a` or `a * b`. Ordinary dihedral groups,
generalized dihedral groups, dicyclic groups and generalized quaternion groups
are all of this form.

## Implementation notes

Built concretely, as an inductive with two constructors mirroring Mathlib's
`DihedralGroup` (`rot`/`refl` against `r`/`sr`), rather than as a
`SemidirectProduct`. The extension is **non-split** exactly when `z ≠ 0` — that
is the dicyclic and quaternion case — so `SemidirectProduct A (ZMod 2)` would
capture only `z = 0` and is the wrong substrate.

Presenting it concretely also discharges for free the source's claim that every
element is *uniquely* `a` or `a * b`: that is `rot`/`refl` injectivity and
disjointness, i.e. constructor injectivity.

`2 • z = 0` is carried as `Fact` because it is genuinely needed for
associativity, not merely for the presentation: with `refl` thrice,
`refl a * (refl a' * refl a'')` reduces to `refl (a - a' + a'' - z)` while
`(refl a * refl a') * refl a''` reduces to `refl (a - a' + a'' + z)`, and these
agree precisely when `z = -z`.

## The concrete model, and the notation used below

Under the presentation above, `rot a` is the element `a` of the abelian
subgroup, and `refl a` is `a * b`, where `b` is the adjoined involution with
`b² = z` and `b a b⁻¹ = a⁻¹` for every `a ∈ A`. So `b` itself is `refl 0`
(`InvExt.b`), and `a⁻¹` is `-a` because `A` is written additively.

The docstrings below write `ι a` for `rot a`, the image of `a` under the
inclusion `InvExt.incl`, and `τ` for `b`, so that `ι a * τ = refl a` by
`rot_mul_refl`. Each `*_mul_*` equation below is one case of the resulting
multiplication table.
-/

@[expose] public section

variable {A : Type*}

/-- The inclusion `ι : A → G_{A,z}` of the abelian subgroup, `ι a = a`.

In the concrete model this is the `rot` constructor on the nose, so it is a
**reducible** abbreviation for it and not a second notion of inclusion: every
consumer continues to see, match on and rewrite with `rot`. -/
@[lyons_tag "def_inv_ext_incl"]
abbrev InvExt.incl {A : Type*} {z : A} : A → InvExt A z := InvExt.rot

namespace InvExt

section Defs

variable [AddCommGroup A] {z : A}

/-- **The abelian part is multiplicative**, `ι a * ι a' = ι (a * a')`. -/
@[lyons_tag "lem_inv_ext_hom", simp]
theorem rot_mul_rot (a a' : A) : (rot a : InvExt A z) * rot a' = rot (a + a') := rfl

@[simp] theorem rot_mul_refl (a a' : A) : (rot a : InvExt A z) * refl a' = refl (a + a') := rfl
@[simp] theorem refl_mul_rot (a a' : A) : (refl a : InvExt A z) * rot a' = refl (a - a') := rfl
@[simp] theorem refl_mul_refl (a a' : A) :
    (refl a : InvExt A z) * refl a' = rot (a - a' + z) := rfl
@[simp] theorem one_def : (1 : InvExt A z) = rot 0 := rfl

/-- **Inverses in the abelian part**, `(ι a)⁻¹ = ι (a⁻¹)`. -/
@[lyons_tag "lem_inv_ext_inv", simp]
theorem inv_rot (a : A) : (rot a : InvExt A z)⁻¹ = rot (-a) := rfl

/-- **Inverses outside the abelian part**, `(ι a * τ)⁻¹ = ι (z * a) * τ`.

Read through `ι a * τ = refl a`; the element `ι (z a) τ` is
`refl (z + a) = refl (a + z)` since `A` is abelian. -/
@[lyons_tag "lem_inv_ext_out_inverse", simp]
theorem inv_refl (a : A) : (refl a : InvExt A z)⁻¹ = refl (a + z) := rfl

end Defs

section Group

variable [AddCommGroup A] {z : A} [hz : Fact (z + z = 0)]

/-- `z` is its own negative, which is what makes multiplication associative. -/
theorem neg_z : -z = (z : A) := neg_eq_of_add_eq_zero_left hz.out

theorem two_zsmul_z : (2 : ℤ) • z = 0 := by
  rw [two_zsmul]; exact hz.out

theorem two_nsmul_z : (2 : ℕ) • z = 0 := by
  rw [two_nsmul]; exact hz.out

theorem neg_two_zsmul_z : (-2 : ℤ) • z = 0 := by
  rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, neg_zsmul, two_zsmul_z, neg_zero]

/-- `u - z = u + z`, the only consequence of `2z = 0` the group laws need. -/
theorem sub_z (u : A) : u - z = u + z := by rw [sub_eq_add_neg, neg_z]

end Group

section Card

variable [AddCommGroup A] {z : A}

omit [AddCommGroup A] in
/-- `|G_{A,z}| = 2|A|`: every element is uniquely `a` or `a * b`. -/
theorem card [Fintype A] : Fintype.card (InvExt A z) = 2 * Fintype.card A := by
  rw [Fintype.ofEquiv_card]
  simp [Fintype.card_sum, two_mul]

end Card

section Presentation

variable [AddCommGroup A] {z : A} [Fact (z + z = 0)]

/-- The distinguished element `b = τ`, outside the abelian part: the adjoined
involution, which in the concrete model is `refl 0`. -/
@[lyons_tag "not_inv_ext_tau"]
def b : InvExt A z := refl 0

omit [Fact (z + z = 0)] in
/-- **`b² = z`.** One of the two defining relations, `τ² = ι z`. -/
@[lyons_tag "lem_inv_ext_b_sq"]
theorem b_sq : (b : InvExt A z) * b = rot z := by simp [b]

/-- **`b a b⁻¹ = a⁻¹`.** The other defining relation: conjugation by `b`
inverts the abelian part, `τ (ι a) τ⁻¹ = ι (a⁻¹)`. -/
@[lyons_tag "lem_inv_ext_conj_b"]
theorem b_conj (a : A) : (b : InvExt A z) * rot a * b⁻¹ = rot (-a) := by
  have hz' : -z = (z : A) := neg_z
  simp only [b, inv_refl, refl_mul_rot, refl_mul_refl]
  congr 1
  rw [← hz']
  abel

omit [Fact (z + z = 0)] in
/-- Every element outside the abelian part squares to `z`. -/
theorem refl_sq (a : A) : (refl a : InvExt A z) * refl a = rot z := by simp

/-- Conjugation by any element outside the abelian part inverts `A`, which is
why the source may replace `b` by an arbitrary `c ∉ A`:
`(ι d * τ) (ι a) (ι d * τ)⁻¹ = ι (a⁻¹)`, with `ι d * τ = refl d`. -/
@[lyons_tag "lem_inv_ext_conj"]
theorem refl_conj (a a' : A) :
    (refl a : InvExt A z) * rot a' * (refl a)⁻¹ = rot (-a') := by
  have hz' : -z = (z : A) := neg_z
  simp only [inv_refl, refl_mul_rot, refl_mul_refl]
  congr 1
  rw [← hz']
  abel

end Presentation

section Dihedral

variable {n : ℕ}

/-- The extension's standing hypothesis `z² = 1` at `z = 0`, which is what makes
`G_{ℤ/n, 0}` a group and hence the general theory applicable to it. -/
instance instFactZModZeroAddZero : Fact ((0 : ZMod n) + 0 = 0) := ⟨add_zero 0⟩

/-- `G_{ℤ/n, 0}` is the dihedral group of order `2n`.

Mathlib's `sr i` is `b * r^i`, while `refl a` here is `r^a * b = b * r^(-a)`,
which is why the reflection component is negated.

Here `ZMod n` is the cyclic group of order `n` and `z = 0` is its neutral
element. Stated for every `n : ℕ`, including the degenerate `n = 0`. -/
@[lyons_tag "lem_dihedral_iso"]
def dihedralEquiv : InvExt (ZMod n) 0 ≃* DihedralGroup n where
  toFun
    | rot a => .r a
    | refl a => .sr (-a)
  invFun
    | .r a => rot a
    | .sr a => refl (-a)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  map_mul' x y := by
    cases x <;> cases y <;>
      simp only [rot_mul_rot, rot_mul_refl, refl_mul_rot, refl_mul_refl,
        DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;>
      congr 1 <;> abel

end Dihedral

end InvExt
