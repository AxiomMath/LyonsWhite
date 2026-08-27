/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.LinearAlgebra.Lagrange
import Lyons.GroupAlgebra.Sqrt

/-!
# Transferring the functional calculus to another representation

`Lyons.L` is the representation in which every analytic construction of this
development is made: `msqrt`, `mpow` and `powElt` are all defined by applying
Mathlib's continuous functional calculus to `L x`. The dihedral argument then
needs the *same* elements evaluated in a **different** representation, `ρ_k`, and
the group algebra carries no functional calculus of its own to mediate between
them.

## Why the obvious route is unavailable

One would like `StarAlgHomClass.map_cfc`, which pushes `cfc` through a star
homomorphism. It does not apply here: it would need a homomorphism
`Matrix G G ℂ → Matrix (Fin 2) (Fin 2) ℂ`, and for `|G| > 2` no unital one
exists — the matrix algebra is simple, so any unital homomorphism out of it is
injective on a `|G|²`-dimensional algebra. The two representations are
incomparable as targets; only their common *source*, the group algebra, relates
them.

## The route taken: interpolate, then transfer a polynomial

A matrix has finite real spectrum (`Matrix.finite_real_spectrum`), so on the
union of the two spectra any function agrees with a polynomial (Lagrange
interpolation). The functional calculus of a polynomial is `Polynomial.aeval`,
which every algebra homomorphism transfers for free. So the element produced in
one representation is `aeval x q` for a polynomial `q` *in the group algebra*,
and applying the other representation to that element is a rewrite.

The interpolant depends on `f`, on `x`, and on the target representation, and is
never exhibited — it exists only inside these proofs.

## Main results

* `Lyons.exists_polynomial_eqOn` : Lagrange interpolation on a finite set.
* `Lyons.algHom_eq_cfc_of_L` : if `L y = cfc f (L x)`, then `φ y = cfc f (φ x)`
  for any `ℝ`-algebra map `φ` into a matrix algebra.
-/

open Matrix

namespace Lyons

/-- **Lagrange interpolation.** On a finite subset of `ℝ`, every function agrees
with a polynomial. -/
theorem exists_polynomial_eqOn {s : Set ℝ} (hs : s.Finite) (f : ℝ → ℝ) :
    ∃ q : Polynomial ℝ, ∀ r ∈ s, q.eval r = f r := by
  classical
  refine ⟨Lagrange.interpolate hs.toFinset id f, fun r hr => ?_⟩
  exact Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (hs.mem_toFinset.mpr hr)

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **The functional calculus transfers between representations of the group
algebra.** If a group-algebra element `y` realises `cfc f` of `x` in the left
regular representation, then it realises `cfc f` of `x` in *every* representation
by matrices.

Both self-adjointness hypotheses are needed and neither implies the other: `cfc`
is a junk value unless its argument satisfies the predicate, and the predicate
must hold on each side separately, in that side's matrix algebra. -/
theorem algHom_eq_cfc_of_L {m : Type*} [Fintype m] [DecidableEq m]
    (φ : MonoidAlgebra ℝ G →ₐ[ℝ] Matrix m m ℂ) (f : ℝ → ℝ)
    {x y : MonoidAlgebra ℝ G}
    (hL : IsSelfAdjoint (L x)) (hφ : IsSelfAdjoint (φ x))
    (hy : L y = cfc f (L x)) :
    φ y = cfc f (φ x) := by
  classical
  obtain ⟨q, hq⟩ := exists_polynomial_eqOn
    ((Matrix.finite_real_spectrum (A := L x)).union
      (Matrix.finite_real_spectrum (A := φ x))) f
  -- On the left regular side, `cfc f (L x)` is a polynomial in `x`.
  have hLq : cfc f (L x) = L (Polynomial.aeval x q) :=
    calc cfc f (L x) = cfc (fun r : ℝ => q.eval r) (L x) :=
          cfc_congr fun r hr => (hq r (Set.mem_union_left _ hr)).symm
      _ = Polynomial.aeval (L x) q := cfc_polynomial q (L x) hL
      _ = L (Polynomial.aeval x q) := Polynomial.aeval_algHom_apply Lalg x q
  -- Injectivity of `L` identifies `y` with that polynomial, inside the algebra.
  have hxy : y = Polynomial.aeval x q := L_injective (by rw [hy, hLq])
  calc φ y = Polynomial.aeval (φ x) q := by
        rw [hxy, Polynomial.aeval_algHom_apply φ x q]
    _ = cfc (fun r : ℝ => q.eval r) (φ x) := (cfc_polynomial q (φ x) hφ).symm
    _ = cfc f (φ x) := cfc_congr fun r hr => hq r (Set.mem_union_right _ hr)

end Lyons
