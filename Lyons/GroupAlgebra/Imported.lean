/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.CenteredRpow

/-!
# Matrix-exponential and functional-calculus inputs imported from Mathlib

Classical facts about the matrix exponential and the continuous functional
calculus used below, each restated in the shape this development needs and
discharged from Mathlib.

## The topology diamond, and why it is invisible here

`Matrix n n ℂ` carries two topologies: the ambient product topology, which is
what `NormedSpace.exp` is computed in at Mathlib's top level, and the one induced
by the operator norm, which lives in the scoped `Matrix.Norms.Operator` and is
what the `NormedRing`-level exponential lemmas require. A statement and its proof
can land on opposite sides of that diamond, and then `rw` fails on a pattern that
is visibly present; `Lyons.Walk.Kolmogorov` opens the scope for exactly this
reason.

Nothing in this file needs to. `Matrix.exp_conjTranspose`, `Matrix.exp_transpose`
and `Matrix.exp_add_of_commute` are the top-level, product-topology forms whose
proofs hide the choice of norm internally, so citing them keeps every statement
here on the ambient side, where the matrix continuous functional calculus
instance is also found. That is not a convenience: the two cannot be had at once.
`CFC.exp_log`, the natural citation for a functional-calculus logarithm, carries
`[NormedRing A]` *and* `[ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]`, and on
matrices those two hypotheses are unsatisfiable simultaneously — the first forces
the operator scope, inside which the second is no longer found. So
`Lyons.exp_cfc_eq_of_eqOn_log` reproduces Mathlib's three-line argument
(`cfc_comp'` on `exp ∘ log`, then `cfc_id`) over this development's
exponential-to-calculus bridge, `Lyons.cfc_exp_eq_exp`, which was built in
`Lyons.Walk.CenteredRpow` to sidestep the same obstruction. Importing that file
rather than re-deriving the bridge is the reason a `GroupAlgebra` module depends
on a `Walk` one.

## Names

`Lyons.exp_conjTranspose` and `Lyons.exp_transpose` deliberately reuse the names
of the Mathlib lemmas they re-export, as `Lyons.cos_sub_cos` does in
`Lyons.Analysis.Imported`. Files that `open Matrix` — most of this development —
must therefore qualify the one they mean.

## Main results

* `Lyons.exp_conjTranspose` : `e^(Aᴴ) = (e^A)ᴴ`.
* `Lyons.exp_transpose` : `e^(Aᵀ) = (e^A)ᵀ`.
* `Lyons.exp_add_of_mul_comm` : `e^(M+N) = e^M e^N` for commuting `M`, `N`.
* `Lyons.cfc_isHermitian` : the functional calculus of a real-valued function is
  Hermitian.
* `Lyons.spectrum_pos_of_posDef` : the `ℝ`-spectrum of a positive definite matrix
  is strictly positive.
* `Lyons.exp_cfc_eq_of_eqOn_log` : `e^(φ M) = M` when `φ` agrees with `Real.log`
  on the spectrum of a positive definite `M`.
-/

open Matrix
-- `Matrix.PosDef` is an order-theoretic statement about `⟪M η, η⟫ : ℂ`.
open scoped ComplexOrder

namespace Lyons

/-! ### The matrix exponential -/

section Exp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The exponential commutes with the conjugate transpose.** This is Mathlib's
`Matrix.exp_conjTranspose`, specialised to `ℂ` (Mathlib states it for any
topological star ring) and re-exported under a `Lyons` name so that the
downstream computations cite a declaration of this development.

Note that the citation lands on the *top-level* form, whose proof hides the choice
of matrix norm internally, so this statement lives in the ambient product topology
— see the module docstring. -/
@[lyons_tag "lem_ext_exp_conjTranspose"]
theorem exp_conjTranspose (A : Matrix n n ℂ) :
    NormedSpace.exp Aᴴ = (NormedSpace.exp A)ᴴ :=
  Matrix.exp_conjTranspose A

/-- **The exponential commutes with the transpose.** This is Mathlib's
`Matrix.exp_transpose`, specialised to `ℂ` (Mathlib states it for any topological
commutative `ℚ`-algebra) and re-exported for the same reason as
`Lyons.exp_conjTranspose`; together the two give the entrywise-conjugation
identity that the realness of the heat coefficients runs on. -/
@[lyons_tag "lem_ext_exp_transpose"]
theorem exp_transpose (A : Matrix n n ℂ) :
    NormedSpace.exp Aᵀ = (NormedSpace.exp A)ᵀ :=
  Matrix.exp_transpose A

/-- **The exponential of a sum of commuting matrices splits.**

Mathlib's `Matrix.exp_add_of_commute`, which is `NormedSpace.exp_add_of_commute`
with the choice of matrix norm hidden inside its proof — the reason this
statement, unlike `NormedSpace.exp_add_of_commute` itself, needs no scoped
operator norm on `Matrix n n ℂ`.

The hypothesis is written `M * N = N * M` rather than `Commute M N`. The
commutation is a genuine side condition here: at the one place this is used, with
`M = L Y` and `N = -ϱ(1 - P)`, the two exponents are different operators and
commutation is checked by hand from `Y * π_H = π_H * Y = 0`. So it is carried,
not discharged. -/
@[lyons_tag "lem_ext_exp_add_commute"]
theorem exp_add_of_mul_comm {M N : Matrix n n ℂ} (h : M * N = N * M) :
    NormedSpace.exp (M + N) = NormedSpace.exp M * NormedSpace.exp N :=
  Matrix.exp_add_of_commute M N h

end Exp

/-! ### The continuous functional calculus -/

section Cfc

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The functional calculus of a real-valued function is Hermitian.**

Mathlib's `IsSelfAdjoint.cfc`, which asserts exactly that the unital `ℝ`-calculus
lands in the self-adjoint part, with the conclusion turned into the matrix
predicate `Matrix.IsHermitian` (via `IsSelfAdjoint.isHermitian`) that its
consumers and the `Lyons.L_invol` family are stated with.

Neither Hermitianness of `M` nor continuity of `f` is assumed: `cfc` takes the
junk value `0` off its predicate, so both would be unused binders. -/
@[lyons_tag "lem_ext_cfc_selfadjoint"]
theorem cfc_isHermitian (f : ℝ → ℝ) (M : Matrix n n ℂ) : (cfc f M).IsHermitian :=
  (IsSelfAdjoint.cfc (f := f) (a := M)).isHermitian

/-- The `ℝ`-spectrum of a positive definite matrix is strictly positive. The
strict analogue of `Lyons.spectrum_nonneg_of_nonneg`, read off the eigenvalues
through `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`. -/
theorem spectrum_pos_of_posDef {M : Matrix n n ℂ} (hM : M.PosDef) :
    ∀ r ∈ spectrum ℝ M, 0 < r := by
  intro r hr
  obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hr
  exact hM.eigenvalues_pos i

/-- **A functional-calculus logarithm.** If `φ` agrees with `Real.log` on the
spectrum of a positive definite `M`, then `e^(φ M) = M`.

The hypothesis `Matrix.PosDef` — Hermitian with `⟪M η, η⟫ > 0` for every nonzero
`η` — places the spectrum inside `(0, ∞)`, where `Real.log` is continuous and
`Real.exp_log` applies. The function is an arbitrary real `φ` rather than
`Real.log` itself because the consumer must feed the resulting matrix to
`Lyons.cfc_L_conv` and `Lyons.cfc_L_im_eq_zero`, which are stated for an
arbitrary real function; the calculus only sees the values on the spectrum, so
`cfc_congr` reduces to `Real.log` at no cost.

Mathlib's own statement is `CFC.log` together with `CFC.exp_log`, and it is
**unusable at matrices**: `CFC.exp_log` needs `[NormedRing A]` and
`[ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]` at once, and on
`Matrix n n ℂ` the first forces the scoped operator norm, inside which the second
is not found. So its three-line proof is reproduced here over
`Lyons.cfc_exp_eq_exp`, this development's ambient-topology bridge from `cfc
Real.exp` to `NormedSpace.exp`. -/
@[lyons_tag "lem_ext_cfc_log"]
theorem exp_cfc_eq_of_eqOn_log {M : Matrix n n ℂ} (hM : M.PosDef) {φ : ℝ → ℝ}
    (hφ : ∀ r ∈ spectrum ℝ M, φ r = Real.log r) :
    NormedSpace.exp (cfc φ M) = M := by
  have hher : M.IsHermitian := hM.isHermitian
  have hsa : IsSelfAdjoint M := hher
  have hlog : ContinuousOn Real.log (spectrum ℝ M) :=
    Real.continuousOn_log.mono fun r hr => (spectrum_pos_of_posDef hM r hr).ne'
  have hexp : ContinuousOn Real.exp (Real.log '' spectrum ℝ M) :=
    Real.continuous_exp.continuousOn
  rw [cfc_congr hφ, ← cfc_exp_eq_exp _ (cfc_isHermitian Real.log M),
    ← cfc_comp' Real.exp Real.log M hexp hlog hsa]
  rw [cfc_congr (f := fun r => Real.exp (Real.log r)) (g := fun r => r)
      fun r hr => Real.exp_log (spectrum_pos_of_posDef hM r hr),
    cfc_id' ℝ M hsa]

end Cfc

end Lyons
