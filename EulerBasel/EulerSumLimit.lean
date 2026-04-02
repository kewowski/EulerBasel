/-
EulerBasel/EulerSumLimit.lean

N → ∞ packaging for the Euler partial sums `eulerSum`.

In this snapshot, we package the N → ∞ passage using `HasSum`/`tsum`
(to avoid snapshot-dependent `Tendsto` lemma names).

Exports:
- summability of the real series
- `HasSum`/`tsum` identities for the coerced ℂ-series
- the `tsum` identity used by the coefficient comparison layer
-/

import EulerBasel.ProductQuadratic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module

open scoped Topology BigOperators
open Filter

namespace EulerBasel

noncomputable section

/-- The Euler term `1/((n:ℂ)+1)^2`. -/
def eulerTerm (n : ℕ) : ℂ :=
  (1 : ℂ) / ((n : ℂ) + 1) ^ 2

/-- Real version, written in the inv-square form your snapshot prefers. -/
def eulerTermR (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) ^ 2)⁻¹

lemma eulerSum_eq_sum_range (N : ℕ) :
    eulerSum N = (Finset.range N).sum (fun n : ℕ => eulerTerm n) := by
  simp [eulerSum, eulerTerm]

/-- `eulerTerm` is `eulerTermR` coerced into `ℂ`. -/
lemma eulerTerm_eq_ofReal (n : ℕ) :
    eulerTerm n = (eulerTermR n : ℂ) := by
  -- Put both sides into the same “inv of square” shape.
  simp [eulerTerm, eulerTermR, div_eq_mul_inv, pow_two]

/-- Summability of the real series `((n+1)^2)⁻¹`. -/
lemma summable_eulerTermR : Summable eulerTermR := by
  -- Exact pattern from Mathlib/Analysis/SpecialFunctions/Stirling.lean (your rg hit).
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := (2 : ℕ))).mpr one_lt_two
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr h0
  -- Rewrite `1 / x^2` into `(x^2)⁻¹` and `(n+1 : ℕ)` into `(n:ℝ)+1`.
  simpa [eulerTermR, one_div, Nat.cast_add, Nat.cast_one, add_assoc] using h1

/-- `HasSum` for the real Euler term. -/
lemma hasSum_eulerTermR :
    HasSum eulerTermR (∑' n : ℕ, eulerTermR n) :=
  summable_eulerTermR.hasSum

/-- Partial sums of `eulerTermR` converge to the `tsum`. -/
lemma tendsto_sum_range_eulerTermR :
    Tendsto (fun N : ℕ => (Finset.range N).sum (fun n : ℕ => eulerTermR n))
      atTop (𝓝 (∑' n : ℕ, eulerTermR n)) := by
  simpa using (hasSum_eulerTermR.tendsto_sum_nat)

/-- `HasSum` for the coerced complex series. -/
lemma hasSum_eulerTermR_coe :
    HasSum (fun n : ℕ => (eulerTermR n : ℂ))
      ((∑' n : ℕ, eulerTermR n : ℝ) : ℂ) := by
  -- In this snapshot `HasSum.mapL` expects the linear map first, then the `HasSum` proof.
  -- (This is exactly what your error message indicates.)
  simpa [Function.comp] using (HasSum.mapL Complex.ofRealCLM hasSum_eulerTermR)

/-- The coerced `tsum` identity. -/
theorem tsum_eulerTermR_coe :
    (∑' n : ℕ, (eulerTermR n : ℂ)) = ((∑' n : ℕ, eulerTermR n : ℝ) : ℂ) :=
  HasSum.tsum_eq hasSum_eulerTermR_coe

/-- The Euler partial sums `eulerSum N` converge to the `tsum` of `eulerTerm`. -/
lemma tendsto_eulerSum :
    Tendsto (fun N : ℕ => eulerSum N) atTop (𝓝 (∑' n : ℕ, eulerTerm n)) := by
  -- Use the `HasSum`-to-`Tendsto` packaging, but keep it snapshot-stable.
  have hsumm_coe : Summable (fun n : ℕ => (eulerTermR n : ℂ)) :=
    hasSum_eulerTermR_coe.summable
  have hsumm : Summable (fun n : ℕ => eulerTerm n) := by
    simpa [eulerTerm_eq_ofReal] using hsumm_coe
  have hhas : HasSum (fun n : ℕ => eulerTerm n) (∑' n : ℕ, eulerTerm n) :=
    hsumm.hasSum

  -- Convert `eulerSum` to the `Finset.range` partial sums and apply `tendsto_sum_nat`.
  have ht :
      Tendsto (fun N : ℕ => (Finset.range N).sum (fun n : ℕ => eulerTerm n))
        atTop (𝓝 (∑' n : ℕ, eulerTerm n)) := by
    simpa using (hhas.tendsto_sum_nat)

  simpa [eulerSum_eq_sum_range] using ht


/-- The `tsum` of the complex Euler term equals the coercion of the real `tsum`. -/
theorem tsum_eulerTerm_eq_coe_tsum_real :
    (∑' n : ℕ, eulerTerm n) = ((∑' n : ℕ, eulerTermR n : ℝ) : ℂ) := by
  -- rewrite the summand, then use the previous identity
  have hcongr : (fun n : ℕ => eulerTerm n) = fun n : ℕ => (eulerTermR n : ℂ) := by
    funext n
    simp [eulerTerm_eq_ofReal]
  simpa [hcongr] using tsum_eulerTermR_coe


end
end EulerBasel


