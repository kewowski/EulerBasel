/-
EulerBasel/EulerProductExpansion.lean

Foundational finite Euler product layer.

Constraints:
- Must remain below the `Coefficient*` pipeline to avoid import cycles.
- Do not define `sineTerm` here; Mathlib’s `_root_.sineTerm` is used later, and shadowing it breaks rewrites.

Provides:
- `eulerFactor z n = 1 - z^2 / (n+1)^2`
- `eulerProd z N = ∏ n < N, eulerFactor z n`
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace EulerBasel

open scoped BigOperators

noncomputable section

/-- The Euler factor in the `1 - z^2/(n+1)^2` form. -/
def eulerFactor (z : ℂ) (n : ℕ) : ℂ :=
  1 - z ^ 2 / ((n : ℂ) + 1) ^ 2

/-- The finite Euler product `∏_{n < N} (1 - z^2/(n+1)^2)`. -/
def eulerProd (z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, eulerFactor z n

end

end EulerBasel




