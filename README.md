[![](logo.svg)](https://axiommath.ai/)

# Proof of the Lyons-White Conjecture

This is a Lean formalization of the rate-monotonicity of even-exponent distances for
continuous-time random walks, and of its failure at every other exponent above 1.

## Main Results

* For all positive integers `n` and `m`, raising the jump rates of a symmetric walk on the
  dihedral group `D_n` cannot increase the `ℓ^{2m}` distance of its time-`t` distribution
  from uniform.
* The same holds over every inversion extension of a finite abelian group by an involution,
  a family including the generalized dihedral, dicyclic and generalized quaternion groups.
* For every real `p > 1` that is not an even integer, there is an `n` for which the pair
  `(D_n, p)` is not rate-monotonic.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependency above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
