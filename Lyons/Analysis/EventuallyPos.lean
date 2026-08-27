/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A positive one-sided limit is positive near the endpoint

A function with a strictly positive limit along `𝓝[>] 0` is strictly positive on
some `Ioo 0 t₀`. This small manoeuvre is needed twice downstream — once in the
perturbation parameter `ε`, once in the regularisation parameter `ς` — so it is
stated here once, for an arbitrary real function, rather than repeating the
filter plumbing at both places.

## The shape of the conclusion

Stated as `0 < t → t < t₀ → 0 < F t` rather than `t ∈ Set.Ioo 0 t₀`, matching how
`Lyons.Converse.exists_energy_testElement_pos` states its own conclusion — the
two are the same statement, and the unbundled form is what the consumers actually
apply.

## Why `L / 2`

The obvious route, "the limit is positive so the function eventually is", needs a
strict bound to hand to `Filter.Tendsto.eventually_const_lt`; `L / 2` is the
usual choice. Any constant in `(0, L)` would serve.
-/

open Filter Topology

namespace Lyons

/-- **A function with a positive limit from the right is positive just to the
right.** If `F t → L` as `t → 0⁺` and `L > 0`, then there is `t₀ > 0` with
`F t > 0` for every `t ∈ (0, t₀)`.

Extracted from the proof of `Lyons.Converse.exists_energy_testElement_pos`,
which needs it in the perturbation parameter `ε`, so that it can be reused in
the regularisation parameter `ς` rather than repeating the argument. -/
theorem exists_pos_of_tendsto_nhdsGT {F : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (h : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → 0 < F t := by
  have hev := h.eventually_const_lt (u := L / 2) (by linarith)
  obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (Filter.eventually_iff.mp hev)
  refine ⟨t₀, ht₀, fun t ht htlt => ?_⟩
  have : L / 2 < F t := hsub ⟨ht, htlt⟩
  linarith

end Lyons
