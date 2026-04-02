/-
EulerBasel/NearZeroSegment.lean

Scaling/segment facts for the punctured ball `nearZeroPunctured`.

Key lemma:
  if z ∈ nearZeroPunctured and s ∈ Ioc (0:ℝ) 1, then (s:ℂ) * z ∈ nearZeroPunctured.

No project files are edited.
-/

import EulerBasel.CoefficientEulerLicensing

open scoped Topology Interval
open Filter

namespace EulerBasel

noncomputable section

/-- Scaling a point in `nearZeroPunctured` by `s ∈ (0,1]` stays in `nearZeroPunctured`. -/
lemma segMul_mem_nearZeroPunctured
    {z : ℂ} (hz : z ∈ nearZeroPunctured)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ((s : ℂ) * z) ∈ nearZeroPunctured := by
  -- unpack hypotheses
  have hz' : ‖z‖ < (1 / 2 : ℝ) ∧ z ≠ 0 :=
    (mem_nearZeroPunctured_iff (z := z)).1 hz
  have hspos : 0 < s := hs.1
  have hsle : s ≤ 1 := hs.2

  -- show nonzero
  have hsne : (s : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hspos)
  have hszne : (s : ℂ) * z ≠ 0 := mul_ne_zero hsne hz'.2

  -- norm bound: ‖(s:ℂ) * z‖ < 1/2
  have habs_le : |s| ≤ (1 : ℝ) := by
    have hsnonneg : 0 ≤ s := le_of_lt hspos
    simpa [abs_of_nonneg hsnonneg] using hsle

  have hnorm_s_le : ‖(s : ℂ)‖ ≤ (1 : ℝ) := by
    -- `‖(s:ℂ)‖ = |s|`
    simpa using habs_le

  have hnorm_mul_le : ‖(s : ℂ) * z‖ ≤ ‖z‖ := by
    -- ‖s*z‖ = ‖s‖*‖z‖ ≤ 1*‖z‖ = ‖z‖
    have : ‖(s : ℂ)‖ * ‖z‖ ≤ (1 : ℝ) * ‖z‖ :=
      mul_le_mul_of_nonneg_right hnorm_s_le (norm_nonneg z)
    simpa [norm_mul, one_mul, mul_assoc] using this

  have hnorm_lt : ‖(s : ℂ) * z‖ < (1 / 2 : ℝ) :=
    lt_of_le_of_lt hnorm_mul_le hz'.1

  -- pack back into membership
  exact (mem_nearZeroPunctured_iff (z := (s : ℂ) * z)).2 ⟨hnorm_lt, hszne⟩

/--
Same lemma but with the `[[0,1]]` (uIcc) binder.

We assume additionally `s ≠ 0` so that `0 < s`.
-/
lemma segMul_mem_nearZeroPunctured_uIcc
    {z : ℂ} (hz : z ∈ nearZeroPunctured)
    {s : ℝ} (hs : s ∈ [[(0 : ℝ), (1 : ℝ)]]) (hs0 : s ≠ 0) :
    ((s : ℂ) * z) ∈ nearZeroPunctured := by
  have hsIcc : (0 : ℝ) ≤ s ∧ s ≤ 1 := by
    simpa [Set.uIcc,
      min_eq_left (show (0 : ℝ) ≤ 1 by exact zero_le_one),
      max_eq_right (show (0 : ℝ) ≤ 1 by exact zero_le_one)] using hs

  have hs0le : 0 ≤ s := hsIcc.1
  have hsle1 : s ≤ 1 := hsIcc.2
  have hspos : 0 < s := lt_of_le_of_ne hs0le (Ne.symm hs0)

  have hsIoc : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hspos, hsle1⟩
  exact segMul_mem_nearZeroPunctured (z := z) hz hsIoc

end

end EulerBasel
