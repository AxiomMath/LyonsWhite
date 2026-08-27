/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Lyons.Fourier.AddCharBasic
import Lyons.GroupAlgebra.Sqrt
import Lyons.InversionExtension.Basic

/-!
# The two-dimensional representations of an inversion extension

For a finite abelian group `A`, an involution `z ∈ A` and a character
`χ : AddChar A ℂ`, the inversion extension `Lyons.InvExt A z` carries a
two-dimensional unitary representation

* `ι a = rot a  ↦  Dchi χ a = diag (χ a, conj (χ a))`,
* `ι a * τ = refl a  ↦  Dchi χ (a - d) * Bchi χ z`,   `Bchi χ z = !![0, χ z; 1, 0]`

for each choice of a distinguished outside element `ι d * τ = refl d`, which
`Bchi χ z` is the image of. This file builds it, extends it to the real group
algebra, and reads off the block form of a self-adjoint element.

## Main definitions

* `Lyons.InvExtBlock.Dchi`, `Lyons.InvExtBlock.Bchi` : the diagonal and twist
  blocks.
* `Lyons.InvExtBlock.rho`, `Lyons.InvExtBlock.rhoAlg` : the representation on
  the group and on the group algebra.
* `Lyons.InvExtBlock.uCoeff`, `Lyons.InvExtBlock.vCoeff` : the abelian and
  outside coefficient functions.
* `Lyons.InvExtBlock.Ublock`, `Lyons.InvExtBlock.Vblock` : their Fourier
  transforms.

## Main results

* `Lyons.InvExtBlock.rhoAlg_invol` : `ρ` is a star homomorphism.
* `Lyons.InvExtBlock.rhoAlg_entries` : the four entries of `ρ(y)` for an
  arbitrary `y`.
* `Lyons.InvExtBlock.Vblock_twist`, `Lyons.InvExtBlock.Vblock_eq_zero` : the
  outside transform is twisted by the sign of `z`, and vanishes at an odd
  character.
* `Lyons.InvExtBlock.rhoAlg_block` : the Hermitian block form.
* `Lyons.InvExtBlock.Ublock_ge_norm_Vblock` : positivity dominates the outside
  transform.

## Where `z` enters, and why the layer splits

`Bchi χ z` squares to `χ z • 1`, not to `1`. For the dihedral group `z = 0`, so
`χ z = 1` for every character and `Bchi` is the permutation matrix appearing in
the dihedral `Lyons.rhoFun`. In general `χ z = ±1` — that is `char_involution` —
and the sign propagates:

* self-adjointness of `x` becomes **two** statements, `uCoeff_neg`
  (`u_{-a} = u_a`) and `vCoeff_involution_add` (`v_{z + a} = v_a`). The second is
  vacuous when `z = 0`, which is why the dihedral development has only the
  first;
* the outside transform satisfies `V = χ z * V`, hence **vanishes** at every
  character with `χ z = -1`. That is `Vblock_eq_zero`, and it has no dihedral
  analogue at all.

## Implementation notes

`A` is written additively here and multiplicatively in the source, so the
source's `ι(a)` is `InvExt.rot a`, its `ι(a)τ` is `InvExt.refl a`, its `a^{-1}`
is `-a` and its `z^2 = 1` is `z + z = 0` (carried as `Fact`, as in
`Lyons.InversionExtension.Basic`). Under that dictionary the source's
`ρ_{χ,d}((a,1)) = D_χ(ad^{-1})B_χ` is `Dchi χ (a - d) * Bchi χ z`.

Positivity is **not** transported by exhibiting an intertwiner into the regular
representation. `IsPos x` is defined through `L x`, and `rho` is unrelated to
`L`; what makes positivity transferable is the factorisation `x = x^⋆ x` inside
the group algebra (`Lyons.eq_invol_mul_self`, via the functional calculus of
`Lyons.GroupAlgebra.Sqrt`), which any star homomorphism carries to a
positive semidefinite matrix. This is the route the dihedral
`Lyons.rhoAlg_posSemidef` already takes.
-/

open Finset Matrix
open scoped ComplexConjugate

namespace Lyons.InvExtBlock

variable {A : Type*} [AddCommGroup A] {z : A}

/-! ### Character values at an involution -/

/-- **Characters of an involution are signs.**

Stated with `z + z = 0` as an explicit hypothesis rather than through `Fact`,
because it is used below both inside and outside the scope where the group
structure of `InvExt A z` is available. -/
@[lyons_tag "lem_char_involution"]
theorem char_involution (χ : AddChar A ℂ) (hz : z + z = 0) : χ z = 1 ∨ χ z = -1 := by
  refine mul_self_eq_one_iff.mp ?_
  rw [← AddChar.map_add_eq_mul, hz, AddChar.map_zero_eq_one]

/-- The square of `χ z` is `1`. -/
theorem char_involution_sq (χ : AddChar A ℂ) (hz : z + z = 0) : χ z * χ z = 1 := by
  rw [← AddChar.map_add_eq_mul, hz, AddChar.map_zero_eq_one]

/-- `χ z` is real, being `±1`. -/
theorem conj_char_involution (χ : AddChar A ℂ) (hz : z + z = 0) :
    conj (χ z) = χ z := by
  rcases char_involution χ hz with h | h <;> rw [h] <;> simp

/-! ### The two blocks -/

section Blocks

/-- The **diagonal character block** `diag (χ a, conj (χ a))`. -/
@[lyons_tag "def_D_chi"]
def Dchi (χ : AddChar A ℂ) (a : A) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![χ a, 0; 0, conj (χ a)]

/-- The **twist block** `!![0, χ z; 1, 0]`, the image of the distinguished
outside element.

For `z = 0` this is the permutation matrix `!![0, 1; 1, 0]` of the dihedral
development; the entry `χ z` is where the involution enters the representation
theory. -/
@[lyons_tag "def_B_chi"]
def Bchi (χ : AddChar A ℂ) (z : A) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, χ z; 1, 0]

variable {χ : AddChar A ℂ}

@[simp] theorem Dchi_zero : Dchi χ (0 : A) = 1 := by
  rw [Dchi, AddChar.map_zero_eq_one, map_one, Matrix.one_fin_two]

/-- `Dchi` is multiplicative: `χ` is, and so is conjugation. -/
theorem Dchi_mul (a a' : A) : Dchi χ a * Dchi χ a' = Dchi χ (a + a') := by
  rw [Dchi, Dchi, Dchi, Matrix.mul_fin_two, AddChar.map_add_eq_mul, map_mul]
  norm_num

/-- `Bchi` squares to `χ z • 1`, which is `Dchi χ z` because `χ z` is real.
This is the source's second matrix identity `B² = χ(z)I = E(z)`. -/
theorem Bchi_mul_self (hz : z + z = 0) : Bchi χ z * Bchi χ z = Dchi χ z := by
  rw [Bchi, Dchi, Matrix.mul_fin_two, conj_char_involution χ hz]
  norm_num

/-- `Bchi` is unitary up to the sign `χ z`: its conjugate transpose is
`χ z • Bchi`. For `χ z = 1` this says `Bchi` is self-adjoint; the other sign is
what the star computation on `refl` has to carry. -/
theorem Bchi_conjTranspose (hz : z + z = 0) : (Bchi χ z)ᴴ = χ z • Bchi χ z := by
  have hsq : χ z * χ z = 1 := char_involution_sq χ hz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bchi, Matrix.conjTranspose_apply, conj_char_involution χ hz, hsq]

/-- `Dchi` at the involution is the scalar `χ z`, because `χ z` is real. -/
theorem Dchi_involution (hz : z + z = 0) :
    Dchi χ z = χ z • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Dchi, conj_char_involution χ hz, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem Dchi_mul_out (a a' : A) :
    Dchi χ a * (Dchi χ a' * Bchi χ z) = Dchi χ (a + a') * Bchi χ z := by
  rw [← mul_assoc, Dchi_mul]

variable [Fintype A]

/-- Conjugating a character value negates its argument. The values of a
character of a *finite* group are roots of unity, which is what makes this
available with no explicit root-of-unity form; this is
`AddChar.map_neg_eq_conj`. -/
theorem char_neg (a : A) : χ (-a) = conj (χ a) := AddChar.map_neg_eq_conj χ a

theorem Dchi_conjTranspose (a : A) : (Dchi χ a)ᴴ = Dchi χ (-a) := by
  rw [Dchi, Dchi, char_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **`Bchi` inverts the diagonal block it passes**, the matrix form of
`τ (ι a) τ⁻¹ = ι (a⁻¹)`. This is the source's third matrix identity
`B E(a) = E(a⁻¹) B`. -/
theorem Bchi_mul_Dchi (a : A) : Bchi χ z * Dchi χ a = Dchi χ (-a) * Bchi χ z := by
  rw [Bchi, Dchi, Dchi, char_neg, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num [mul_comm]

/-! ### Products of images

The multiplicativity check reduces to three products of the shapes
`E(a)E(a')`, `E(a)B · E(a')` and `E(a)B · E(a')B`. The last two are recorded
here so that the four cases of the multiplication table below are each a single
rewrite plus an `abel`. -/

theorem out_mul_Dchi (a a' : A) :
    Dchi χ a * Bchi χ z * Dchi χ a' = Dchi χ (a - a') * Bchi χ z := by
  calc Dchi χ a * Bchi χ z * Dchi χ a'
      = Dchi χ a * (Bchi χ z * Dchi χ a') := mul_assoc ..
    _ = Dchi χ a * (Dchi χ (-a') * Bchi χ z) := by rw [Bchi_mul_Dchi]
    _ = Dchi χ (a - a') * Bchi χ z := by rw [Dchi_mul_out, sub_eq_add_neg]

theorem out_mul_out (hz : z + z = 0) (a a' : A) :
    Dchi χ a * Bchi χ z * (Dchi χ a' * Bchi χ z) = Dchi χ (a - a' + z) := by
  calc Dchi χ a * Bchi χ z * (Dchi χ a' * Bchi χ z)
      = Dchi χ a * Bchi χ z * Dchi χ a' * Bchi χ z := (mul_assoc ..).symm
    _ = Dchi χ (a - a') * Bchi χ z * Bchi χ z := by rw [out_mul_Dchi]
    _ = Dchi χ (a - a') * Dchi χ z := by rw [mul_assoc, Bchi_mul_self hz]
    _ = Dchi χ (a - a' + z) := Dchi_mul ..

omit [Fintype A] in
/-- `Dchi χ c * Bchi χ z` written out. The image of an outside basis element,
whose four entries the block form reads off. -/
theorem Dchi_mul_Bchi (c : A) :
    Dchi χ c * Bchi χ z = !![0, χ z * χ c; conj (χ c), 0] := by
  rw [Dchi, Bchi, Matrix.mul_fin_two]
  norm_num [mul_comm]

end Blocks

/-! ### The representation -/

section Rep

variable [Fintype A]

/-- The underlying function of `ρ_{χ,d}`: the abelian part goes to the diagonal
block, and the outside part to a diagonal block times the twist, normalised so
that the distinguished outside element `ι d * τ = refl d` goes to `Bchi χ z`.
The source's `ρ_{χ,d}((a,1)) = D_χ(ad^{-1})B_χ` is the second line. -/
def rhoFun (χ : AddChar A ℂ) (d : A) : InvExt A z → Matrix (Fin 2) (Fin 2) ℂ
  | .rot a => Dchi χ a
  | .refl a => Dchi χ (a - d) * Bchi χ z

omit [Fintype A] in
@[simp] theorem rhoFun_rot (χ : AddChar A ℂ) (d a : A) :
    rhoFun χ d (.rot a : InvExt A z) = Dchi χ a := rfl

omit [Fintype A] in
@[simp] theorem rhoFun_refl (χ : AddChar A ℂ) (d a : A) :
    rhoFun χ d (.refl a : InvExt A z) = Dchi χ (a - d) * Bchi χ z := rfl

variable [hz : Fact (z + z = 0)]

/-- **The two-dimensional representation `ρ_{χ,d}`** of the inversion extension.

The content beyond the prescription on the basis is that `rhoFun` respects the
multiplication table, which is what bundling it as a `MonoidHom` records.

Unlike the cyclic `Lyons.rho`, this `ρ` is indexed by a *character* of a general
finite abelian `A` and carries the second index `d`. -/
@[lyons_tag "def_rho"]
def rho (χ : AddChar A ℂ) (d : A) : InvExt A z →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := rhoFun χ d
  map_one' := by rw [InvExt.one_def, rhoFun_rot, Dchi_zero]
  map_mul' x y := by
    cases x with
    | rot a =>
      cases y with
      | rot a' => rw [InvExt.rot_mul_rot, rhoFun_rot, rhoFun_rot, rhoFun_rot, Dchi_mul]
      | refl a' =>
        have harg : a + (a' - d) = a + a' - d := by abel
        rw [InvExt.rot_mul_refl, rhoFun_refl, rhoFun_rot, rhoFun_refl, Dchi_mul_out,
          harg]
    | refl a =>
      cases y with
      | rot a' =>
        have harg : a - d - a' = a - a' - d := by abel
        rw [InvExt.refl_mul_rot, rhoFun_refl, rhoFun_refl, rhoFun_rot, out_mul_Dchi,
          harg]
      | refl a' =>
        have harg : a - d - (a' - d) + z = a - a' + z := by abel
        rw [InvExt.refl_mul_refl, rhoFun_rot, rhoFun_refl, rhoFun_refl,
          out_mul_out hz.out, harg]

@[simp] theorem rho_apply (χ : AddChar A ℂ) (d : A) (g : InvExt A z) :
    rho χ d g = rhoFun χ d g := rfl

/-- The distinguished outside element of `ρ_{χ,d}` is `ι d * τ`, not `τ`, and it
is what goes to the twist block. This is the whole purpose of the second index:
every block statement below then holds at an arbitrary element outside the image
of `ι`, which the reflection inequality needs. -/
theorem rho_refl_self (χ : AddChar A ℂ) (d : A) :
    rho χ d (.refl d : InvExt A z) = Bchi χ z := by
  rw [rho_apply, rhoFun_refl, sub_self, Dchi_zero, one_mul]

/-- **Each `rho χ d g` is unitary**: inverses go to conjugate transposes. This
is the group-level half of star-preservation.

The `refl` case is where `χ z ≠ 1` shows up: `Bchi` is not self-adjoint, only
self-adjoint up to `χ z`, and that sign is exactly cancelled by the `z` in
`(ι a * τ)⁻¹ = ι (z * a) * τ`. -/
theorem rho_inv (χ : AddChar A ℂ) (d : A) (g : InvExt A z) :
    rho χ d g⁻¹ = (rho χ d g)ᴴ := by
  cases g with
  | rot a => rw [InvExt.inv_rot, rho_apply, rho_apply, rhoFun_rot, rhoFun_rot,
      Dchi_conjTranspose]
  | refl a =>
    have harg : a + z - d = a - d + z := by abel
    calc rho χ d (InvExt.refl a)⁻¹
        = Dchi χ (a - d) * Dchi χ z * Bchi χ z := by
          rw [InvExt.inv_refl, rho_apply, rhoFun_refl, harg, Dchi_mul]
      _ = χ z • (Dchi χ (a - d) * Bchi χ z) := by
          rw [Dchi_involution hz.out, Matrix.mul_smul, mul_one, Matrix.smul_mul]
      _ = (Bchi χ z)ᴴ * (Dchi χ (a - d))ᴴ := by
          rw [Bchi_conjTranspose hz.out, Dchi_conjTranspose, Matrix.smul_mul,
            Bchi_mul_Dchi, neg_neg]
      _ = (rho χ d (InvExt.refl a))ᴴ := by
          rw [rho_apply, rhoFun_refl, Matrix.conjTranspose_mul]

/-- `ρ_{χ,d}` extended to the real group algebra, as an `ℝ`-algebra
homomorphism. At the algebra level `ρ` is defined on `ℝ[G]` by linearity from
its values on the basis, which is what `MonoidAlgebra.lift` performs. -/
@[lyons_tag "def_rho"]
noncomputable def rhoAlg (χ : AddChar A ℂ) (d : A) :
    MonoidAlgebra ℝ (InvExt A z) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  MonoidAlgebra.lift ℝ (Matrix (Fin 2) (Fin 2) ℂ) (InvExt A z) (rho χ d)

@[simp] theorem rhoAlg_single (χ : AddChar A ℂ) (d : A) (g : InvExt A z) (c : ℝ) :
    rhoAlg χ d (MonoidAlgebra.single g c) = c • rho χ d g :=
  MonoidAlgebra.lift_single (rho χ d) g c

/-- **`ρ_{χ,d}` is a unital star homomorphism.** Together with `rhoAlg` being an
`ℝ`-algebra homomorphism, this is the statement that `ρ_{χ,d}` is a unital
`*`-representation of `ℝ[G_{A,z}]`.

The proof reduces to `rho_inv` on basis elements: `invol` sends `g` to `g⁻¹`
without conjugating, the coefficients being real, and `rho_inv` says each
`rho χ d g` is unitary. -/
@[lyons_tag "lem_rho_welldef"]
theorem rhoAlg_invol (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) :
    rhoAlg χ d (invol x) = (rhoAlg χ d x)ᴴ := by
  classical
  -- Freeze the coefficient function: rewriting with `hx` below must not reach
  -- the `co x g` occurrences inside it.
  set c : InvExt A z → ℝ := co x with hc
  have hx : x = ∑ g : InvExt A z, MonoidAlgebra.single g (c g) := by
    refine co_injective fun h ↦ ?_
    rw [co_sum, Finset.sum_eq_single h]
    · simp [hc]
    · intro b _ hb; simp [Ne.symm hb]
    · intro hcon; exact absurd (Finset.mem_univ h) hcon
  have hinv : invol x = ∑ g : InvExt A z, MonoidAlgebra.single g⁻¹ (c g) := by
    refine co_injective fun h ↦ ?_
    rw [co_invol, co_sum, Finset.sum_eq_single h⁻¹]
    · simp [hc]
    · intro b _ hb
      have hne : h ≠ b⁻¹ := fun hcon => hb (by rw [hcon, inv_inv])
      simp [hne]
    · intro hcon; exact absurd (Finset.mem_univ h⁻¹) hcon
  rw [hinv, hx, map_sum, map_sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [rhoAlg_single, rhoAlg_single, rho_inv, Matrix.conjTranspose_smul]
  simp

end Rep

/-! ### Coefficients along the normal form, and their transforms -/

section Coeff

variable [Fact (z + z = 0)]

/-- The **abelian coefficients** `u^x(a) = x_{ι a}`, complexified.

This is the general-`A` form of the cyclic `Lyons.rotCoeff`. -/
def uCoeff (x : MonoidAlgebra ℝ (InvExt A z)) : A → ℂ :=
  fun a => (co x (.rot a) : ℂ)

/-- The **outside coefficients** `v^{x,d}(a) = x_{ι (a d) τ}`, complexified.
`ι (a d) τ` is `InvExt.refl (a + d)`.

This is the general-`A` form of the cyclic `Lyons.reflCoeff`. -/
def vCoeff (x : MonoidAlgebra ℝ (InvExt A z)) (d : A) : A → ℂ :=
  fun a => (co x (.refl (a + d)) : ℂ)

omit [AddCommGroup A] [Fact (z + z = 0)] in
/-- The abelian coefficients are real: they are coefficients of an element of
the *real* group algebra. -/
@[simp] theorem conj_uCoeff (x : MonoidAlgebra ℝ (InvExt A z)) (a : A) :
    conj (uCoeff x a) = uCoeff x a := Complex.conj_ofReal _

omit [Fact (z + z = 0)] in
/-- The outside coefficients are real, for the same reason. -/
@[simp] theorem conj_vCoeff (x : MonoidAlgebra ℝ (InvExt A z)) (d a : A) :
    conj (vCoeff x d a) = vCoeff x d a := Complex.conj_ofReal _

variable [Fintype A] [DecidableEq A]

/-- The transform of the abelian coefficients.

The frequency domain is the character group `Â` of a general finite abelian `A`,
which is what generalizes the cyclic `Lyons.Ublock`. -/
@[lyons_tag "def_block_transforms"]
noncomputable def Ublock (x : MonoidAlgebra ℝ (InvExt A z)) : AddChar A ℂ → ℂ :=
  AddCharFourier.dft (uCoeff x)

/-- The transform of the outside coefficients, generalizing the cyclic
`Lyons.Vblock` in the same way. -/
@[lyons_tag "def_block_transforms"]
noncomputable def Vblock (x : MonoidAlgebra ℝ (InvExt A z)) (d : A) :
    AddChar A ℂ → ℂ :=
  AddCharFourier.dft (vCoeff x d)

/-! ### Self-adjointness in coordinates

The source's displayed pair `u_{a⁻¹} = u_a` and `v_{za} = v_a`, split into two
lemmas because each states one conclusion. For `z = 0` the second is vacuous,
which is why the dihedral development has only the first. -/

omit [Fintype A] [DecidableEq A] in
/-- **Self-adjointness is evenness of the abelian coefficients.**

The cyclic `Lyons.invol_eq_iff_rotCoeff_even` is an iff, which is available in the
dihedral case only because there the outside
coefficients carry no condition at all; in general the converse needs both
clauses, so what is stated here is the implication. -/
@[lyons_tag "lem_selfadjoint_coords"]
theorem uCoeff_neg (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x) (a : A) :
    uCoeff x (-a) = uCoeff x a := by
  have h := congrArg (fun y => co y (InvExt.rot a : InvExt A z)) hsa
  simp only [co_invol, InvExt.inv_rot] at h
  rw [uCoeff, uCoeff, h]

omit [Fintype A] [DecidableEq A] in
/-- **Self-adjointness twists the outside coefficients by `z`.** This is the
clause with no dihedral analogue: it comes from `(ι a * τ)⁻¹ = ι (z a) * τ`,
which for `z = 0` says every outside element is an involution and imposes
nothing. -/
@[lyons_tag "lem_selfadjoint_coords_out"]
theorem vCoeff_involution_add (x : MonoidAlgebra ℝ (InvExt A z))
    (hsa : invol x = x) (d a : A) : vCoeff x d (z + a) = vCoeff x d a := by
  have h := congrArg (fun y => co y (InvExt.refl (a + d) : InvExt A z)) hsa
  simp only [co_invol, InvExt.inv_refl] at h
  rw [vCoeff, vCoeff, show z + a + d = a + d + z from by abel, h]

end Coeff

/-! ### The block form -/

section Block

variable [Fintype A] [Fact (z + z = 0)]
variable {χ : AddChar A ℂ} {d : A} {y : MonoidAlgebra ℝ (InvExt A z)}

/-- `ρ_{χ,d}` expanded over the group basis. -/
theorem rhoAlg_apply (χ : AddChar A ℂ) (d : A) (y : MonoidAlgebra ℝ (InvExt A z)) :
    rhoAlg χ d y = ∑ g : InvExt A z, co y g • rho χ d g := by
  classical
  conv_lhs => rw [basis_expansion y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ ↦ rhoAlg_single χ d g (co y g)

omit [AddCommGroup A] [Fact (z + z = 0)] in
/-- Splitting a sum over `InvExt A z` into the abelian and the outside half.
This is the normal form `InvExt.sumEquiv` used as a bijection of index sets. -/
theorem sum_invExt {M : Type*} [AddCommMonoid M] (F : InvExt A z → M) :
    ∑ g : InvExt A z, F g = (∑ a : A, F (.rot a)) + ∑ a : A, F (.refl a) := by
  classical
  rw [← Fintype.sum_equiv InvExt.sumEquiv (fun s => F (InvExt.sumEquiv s)) F
    fun _ => rfl, Fintype.sum_sum_type]
  rfl

omit [Fact (z + z = 0)] in
/-- Reindexing a sum over `A` by translation. On the outside half this is the
reindexing `a ↦ ad`, which is what turns the coefficients at `ι a * τ` into the
coefficients `v^{x,d}`. -/
theorem sum_shift {M : Type*} [AddCommMonoid M] (d : A) (F : A → M) :
    ∑ a : A, F a = ∑ a : A, F (a + d) :=
  (Fintype.sum_equiv (Equiv.addRight d) (fun a => F (a + d)) F fun _ => rfl).symm

/-! #### Entries of `ρ_{χ,d}` on basis elements

Extracting one entry of a `!![…]` literal is a `simp` chore; these eight lemmas
do it once so the sums below stay readable. -/

section Entries

variable (χ) (d) (a : A)

@[simp] theorem rho_rot_00 : rho χ d (.rot a : InvExt A z) 0 0 = χ a := by
  rw [rho_apply, rhoFun_rot, Dchi]; simp
@[simp] theorem rho_rot_01 : rho χ d (.rot a : InvExt A z) 0 1 = 0 := by
  rw [rho_apply, rhoFun_rot, Dchi]; simp
@[simp] theorem rho_rot_10 : rho χ d (.rot a : InvExt A z) 1 0 = 0 := by
  rw [rho_apply, rhoFun_rot, Dchi]; simp
@[simp] theorem rho_rot_11 : rho χ d (.rot a : InvExt A z) 1 1 = conj (χ a) := by
  rw [rho_apply, rhoFun_rot, Dchi]; simp
@[simp] theorem rho_refl_00 : rho χ d (.refl a : InvExt A z) 0 0 = 0 := by
  rw [rho_apply, rhoFun_refl, Dchi_mul_Bchi]; simp
@[simp] theorem rho_refl_01 :
    rho χ d (.refl a : InvExt A z) 0 1 = χ z * χ (a - d) := by
  rw [rho_apply, rhoFun_refl, Dchi_mul_Bchi]; simp
@[simp] theorem rho_refl_10 :
    rho χ d (.refl a : InvExt A z) 1 0 = conj (χ (a - d)) := by
  rw [rho_apply, rhoFun_refl, Dchi_mul_Bchi]; simp
@[simp] theorem rho_refl_11 : rho χ d (.refl a : InvExt A z) 1 1 = 0 := by
  rw [rho_apply, rhoFun_refl, Dchi_mul_Bchi]; simp

end Entries

variable [DecidableEq A]

/-- Entry `(0,0)` of `ρ_{χ,d}(y)` is `U^y(χ)`. -/
theorem rhoAlg_entry_00 : rhoAlg χ d y 0 0 = Ublock y χ := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, sum_invExt fun g => (co y g • rho χ d g) 0 0,
    Ublock, AddCharFourier.dft_apply]
  simp only [Matrix.smul_apply, rho_refl_00, smul_zero, Finset.sum_const_zero,
    add_zero, rho_rot_00, Complex.real_smul, uCoeff]

/-- Entry `(1,1)` of `ρ_{χ,d}(y)` is `conj (U^y(χ))`: the abelian coefficients
are real, so the lower-right diagonal entry is the conjugate transform. -/
theorem rhoAlg_entry_11 : rhoAlg χ d y 1 1 = conj (Ublock y χ) := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, sum_invExt fun g => (co y g • rho χ d g) 1 1,
    Ublock, AddCharFourier.dft_apply, map_sum]
  simp only [Matrix.smul_apply, rho_refl_11, smul_zero, Finset.sum_const_zero,
    add_zero, rho_rot_11, Complex.real_smul]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [map_mul, conj_uCoeff, uCoeff]

/-- Entry `(0,1)` of `ρ_{χ,d}(y)` is `χ z * V^{y,d}(χ)`. The sign `χ z` is the
one place the involution survives into an entry of the general block. -/
theorem rhoAlg_entry_01 : rhoAlg χ d y 0 1 = χ z * Vblock y d χ := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, sum_invExt fun g => (co y g • rho χ d g) 0 1,
    Vblock, AddCharFourier.dft_apply]
  simp only [Matrix.smul_apply, rho_rot_01, smul_zero, Finset.sum_const_zero,
    zero_add, rho_refl_01, Complex.real_smul]
  rw [sum_shift d fun a => ((co y (InvExt.refl a) : ℝ) : ℂ) * (χ z * χ (a - d)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [vCoeff, add_sub_cancel_right]
  ring

/-- Entry `(1,0)` of `ρ_{χ,d}(y)` is `conj (V^{y,d}(χ))`. -/
theorem rhoAlg_entry_10 : rhoAlg χ d y 1 0 = conj (Vblock y d χ) := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, sum_invExt fun g => (co y g • rho χ d g) 1 0,
    Vblock, AddCharFourier.dft_apply, map_sum]
  simp only [Matrix.smul_apply, rho_rot_10, smul_zero, Finset.sum_const_zero,
    zero_add, rho_refl_10, Complex.real_smul]
  rw [sum_shift d fun a => ((co y (InvExt.refl a) : ℝ) : ℂ) * conj (χ (a - d))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_mul, conj_vCoeff, vCoeff, add_sub_cancel_right]

/-- **The entries of `ρ_{χ,d}`.**

This holds for an arbitrary `y`, with no self-adjointness, and that is why it is
stated separately: the sandwich of the next section is not self-adjoint, so the
self-adjoint block form below cannot be used on it. -/
@[lyons_tag "lem_rho_entries"]
theorem rhoAlg_entries (χ : AddChar A ℂ) (d : A)
    (y : MonoidAlgebra ℝ (InvExt A z)) :
    rhoAlg χ d y = !![Ublock y χ, χ z * Vblock y d χ;
                      conj (Vblock y d χ), conj (Ublock y χ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoAlg_entry_00, rhoAlg_entry_01, rhoAlg_entry_10, rhoAlg_entry_11]

/-! #### Consequences of self-adjointness for the transforms -/

/-- **The abelian transform of a self-adjoint element is real.**

Two effects coincide here: the coefficients are real, which conjugates the
transform, and they are even, which negates the frequency. -/
@[lyons_tag "lem_U_real"]
theorem conj_Ublock (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x)
    (χ : AddChar A ℂ) : conj (Ublock x χ) = Ublock x χ := by
  calc conj (Ublock x χ) = ∑ a : A, uCoeff x a * χ (-a) := by
        rw [Ublock, AddCharFourier.dft_apply, map_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by
          rw [map_mul, conj_uCoeff, ← char_neg]
    _ = ∑ a : A, uCoeff x (-a) * χ a :=
        Fintype.sum_equiv (Equiv.neg A) _ _ fun a ↦ by simp
    _ = ∑ a : A, uCoeff x a * χ a :=
        Finset.sum_congr rfl fun a _ ↦ by rw [uCoeff_neg x hsa]
    _ = Ublock x χ := rfl

/-- Hence `U^x(χ)` *is* its own real part, which is the form the inequality
below consumes. -/
theorem Ublock_ofReal_re (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x)
    (χ : AddChar A ℂ) : (((Ublock x χ).re : ℝ) : ℂ) = Ublock x χ :=
  Complex.conj_eq_iff_re.mp (conj_Ublock x hsa χ)

omit [DecidableEq A] in
/-- **The outside transform is twisted by the sign of `z`.**

The reindexing is by `a ↦ za`, a bijection of `A` because `z² = 1`; the
character picks up the factor `χ z`, and `vCoeff_involution_add` absorbs the
shift in the coefficients. -/
@[lyons_tag "lem_V_twist"]
theorem Vblock_twist (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x)
    (d : A) (χ : AddChar A ℂ) : Vblock x d χ = χ z * Vblock x d χ := by
  have hterm : ∀ a : A,
      vCoeff x d (z + a) * χ (z + a) = χ z * (vCoeff x d a * χ a) := by
    intro a
    rw [vCoeff_involution_add x hsa d a, AddChar.map_add_eq_mul]
    ring
  calc Vblock x d χ
      = ∑ a : A, vCoeff x d (z + a) * χ (z + a) :=
        (Fintype.sum_equiv (Equiv.addLeft z)
          (fun a => vCoeff x d (z + a) * χ (z + a))
          (fun a => vCoeff x d a * χ a) fun _ ↦ rfl).symm
    _ = ∑ a : A, χ z * (vCoeff x d a * χ a) :=
        Finset.sum_congr rfl fun a _ ↦ hterm a
    _ = χ z * Vblock x d χ := by rw [← Finset.mul_sum]; rfl

omit [DecidableEq A] in
/-- **The outside transform vanishes at an odd character.**

This has no dihedral predecessor: for `D_n` the involution is the neutral
element, so `χ z = 1` for every character and the hypothesis is never met. -/
@[lyons_tag "lem_V_vanishes_odd"]
theorem Vblock_eq_zero (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x)
    (d : A) (χ : AddChar A ℂ) (hχ : χ z = -1) : Vblock x d χ = 0 := by
  have h := Vblock_twist x hsa d χ
  rw [hχ] at h
  linear_combination h / 2

/-- **The Hermitian block form of a self-adjoint element.**

The `χ z` of `rhoAlg_entries` is absorbed by `Vblock_twist` and the conjugate of
`rhoAlg_entry_11` by `conj_Ublock`. -/
@[lyons_tag "lem_rho_block"]
theorem rhoAlg_block (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hsa : invol x = x) :
    rhoAlg χ d x = !![Ublock x χ, Vblock x d χ;
                      conj (Vblock x d χ), Ublock x χ] := by
  rw [rhoAlg_entries, ← Vblock_twist x hsa d χ, conj_Ublock x hsa χ]

end Block

/-! ### Positivity -/

section Pos

open scoped ComplexOrder MatrixOrder

variable [Fintype A] [DecidableEq A] [Fact (z + z = 0)]

/-- **Representations preserve positivity.**

`IsPos x` is positive semidefiniteness of `L x`, and `ρ_{χ,d}` is a
representation unrelated to `L`, so positivity cannot be transported along
`rhoAlg` by any general star-hom argument. What makes it transferable is the
factorisation `x = x^⋆ x` *inside the group algebra*
(`Lyons.eq_invol_mul_self`), which a star homomorphism sends to
`ρ(y)ᴴ ρ(y)` — positive semidefinite for any representation whatsoever. -/
@[lyons_tag "lem_rho_pos"]
theorem rhoAlg_posSemidef (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hx : IsPos x) :
    (rhoAlg χ d x).PosSemidef := by
  rw [eq_invol_mul_self x hx, map_mul, rhoAlg_invol]
  exact Matrix.posSemidef_conjTranspose_mul_self _

-- The two `simp` calls below expand a `2 × 2` matrix literal applied to a test
-- vector. Pinning them to `simp only` requires enumerating the `!![…]` entry
-- lemmas, which is brittle; the flexible-tactic style check is therefore
-- disabled for this declaration, not worked around. Same choice as
-- the dihedral `Lyons.Ublock_ge_norm_Vblock`.
set_option linter.flexible false in
/-- **Positivity dominates the outside transform.** The source's
`U ≥ |V| ≥ 0` is this inequality together with `norm_nonneg`.

For positive self-adjoint `x` the block is the Hermitian matrix
`!![U, V; conj V, U]`, whose eigenvalues are `U ± ‖V‖`; nonnegativity of the
smaller one is the claim. The proof tests the quadratic form against
`![V/‖V‖, -1]`, chosen so that both off-diagonal contributions become `-‖V‖`
rather than an unhelpful complex number.

Nothing here branches on the sign `χ z`: `Vblock_twist` has already absorbed it
into `rhoAlg_block`, and at a character with `χ z = -1` the conclusion is the
degenerate `0 ≤ U` — consistent with `Vblock_eq_zero`. -/
@[lyons_tag "lem_U_ge_absV"]
theorem Ublock_ge_norm_Vblock (χ : AddChar A ℂ) (d : A)
    (x : MonoidAlgebra ℝ (InvExt A z)) (hpos : IsPos x) (hsa : invol x = x) :
    ‖Vblock x d χ‖ ≤ (Ublock x χ).re := by
  have hPSD := rhoAlg_posSemidef χ d x hpos
  have hM : rhoAlg χ d x
      = !![Ublock x χ, Vblock x d χ; conj (Vblock x d χ), Ublock x χ] :=
    rhoAlg_block χ d x hsa
  by_cases hV : Vblock x d χ = 0
  · -- Only `0 ≤ U` is needed; test against the first basis vector.
    have h0 := hPSD.dotProduct_mulVec_nonneg (![1, 0] : Fin 2 → ℂ)
    rw [hM] at h0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    rw [hV, norm_zero]
    exact (Complex.nonneg_iff.mp h0).1
  · have hVpos : (0 : ℝ) < ‖Vblock x d χ‖ := norm_pos_iff.mpr hV
    have h := hPSD.dotProduct_mulVec_nonneg
      (![Vblock x d χ / (‖Vblock x d χ‖ : ℂ), -1] : Fin 2 → ℂ)
    rw [hM] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    -- `conj V * V = ‖V‖ ^ 2` is what collapses the two off-diagonal terms.
    have hsq : conj (Vblock x d χ) * Vblock x d χ
        = ((‖Vblock x d χ‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj']
      norm_cast
    have hne : ((‖Vblock x d χ‖ : ℝ) : ℂ) ≠ 0 := by simpa using hVpos.ne'
    have hexp :
        conj (Vblock x d χ) / ((‖Vblock x d χ‖ : ℝ) : ℂ) *
            (Ublock x χ * (Vblock x d χ / ((‖Vblock x d χ‖ : ℝ) : ℂ))
              + -Vblock x d χ)
          + (Ublock x χ + -(conj (Vblock x d χ) *
              (Vblock x d χ / ((‖Vblock x d χ‖ : ℝ) : ℂ))))
          = 2 * Ublock x χ - 2 * ((‖Vblock x d χ‖ : ℝ) : ℂ) := by
      field_simp
      rw [hsq]
      push_cast
      ring
    rw [hexp] at h
    have hre := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im] at hre
    norm_num at hre
    linarith

end Pos

end Lyons.InvExtBlock
