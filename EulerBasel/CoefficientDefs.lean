/-
EulerBasel/CoefficientDefs.lean

Shared definitions for the Euler–Basel coefficient comparison layer.

This isolates:
- piC
- sinDivPiZ / sinDivPiZ0
- baselTerm / baselSum
- identification of baselSum with EulerSumLimit.eulerTerm tsum
-/

import EulerBasel.EulerSumLimit

noncomputable section
open Classical
open scoped Topology BigOperators
open Filter

namespace EulerBasel

-- π as a complex number (local convenience).
local notation "piC" => ((Real.pi : ℝ) : ℂ)

/-- Euler’s normalized sine ratio: `sin(π z)/(π z)` (raw, no patch at `0`). -/
def sinDivPiZ (z : ℂ) : ℂ :=
  Complex.sin (piC * z) / (piC * z)

/--
A harmless 0-patch of `sin(π z)/(π z)`:
we set the value at `z = 0` to the correct limit `1`.
-/
def sinDivPiZ0 (z : ℂ) : ℂ :=
  if z = 0 then (1 : ℂ) else sinDivPiZ z

/-- The Basel summand in the project’s `(n:ℂ)+1` indexing. -/
def baselTerm (n : ℕ) : ℂ :=
  (1 : ℂ) / ((n : ℂ) + 1) ^ 2

/-- The target Basel series value (complex). -/
def baselSum : ℂ :=
  ∑' n : ℕ, baselTerm n

/-- `baselTerm` is definitionally the same as `EulerSumLimit.eulerTerm`. -/
lemma baselTerm_eq_eulerTerm (n : ℕ) :
    baselTerm n = eulerTerm n := by
  simp [baselTerm, EulerBasel.eulerTerm]

/-- `baselSum` is the same `tsum` as in `EulerSumLimit`. -/
lemma baselSum_eq_tsum_eulerTerm :
    baselSum = (∑' n : ℕ, eulerTerm n) := by
  simp [baselSum, baselTerm_eq_eulerTerm]

/-- The Euler partial sums `eulerSum N` converge to `baselSum`. -/
theorem tendsto_eulerSum_atTop_baselSum :
    Tendsto (fun N : ℕ => eulerSum N) atTop (𝓝 baselSum) := by
  -- First: get `HasSum` (hence `Tendsto`) for the ℂ-series `eulerTerm`.
  have hsC : Summable (fun n : ℕ => (eulerTermR n : ℂ)) :=
    (EulerBasel.hasSum_eulerTermR_coe).summable

  have hs : Summable (fun n : ℕ => eulerTerm n) := by
    refine hsC.congr ?_
    intro n
    -- `eulerTerm_eq_ofReal` gives `eulerTerm n = (eulerTermR n : ℂ)`.
    simpa using (EulerBasel.eulerTerm_eq_ofReal n).symm

  have hHas : HasSum (fun n : ℕ => eulerTerm n) (∑' n : ℕ, eulerTerm n) :=
    hs.hasSum

  have hT :
      Tendsto (fun N : ℕ => (Finset.range N).sum (fun n : ℕ => eulerTerm n))
        atTop (𝓝 (∑' n : ℕ, eulerTerm n)) := by
    simpa using hHas.tendsto_sum_nat

  -- Rewrite partial sums to `eulerSum` and the limit to `baselSum`.
  simp at hT
  exact hT

end EulerBasel
