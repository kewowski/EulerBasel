/-
EulerBasel/CoefficientEulerRationalTsum.lean

Define the Euler rational term
  (2*z)/(z^2 - (n+1)^2)

Show it is summable on `nearZeroPunctured`, and identify the log-derivative
of the limit function as the `tsum` of these rational terms by uniqueness of limits.
-/

import EulerBasel.CoefficientEulerSumLimit
import EulerBasel.EulerRationalBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped Topology BigOperators
open Filter

namespace EulerBasel

noncomputable section

/-- Euler’s rational log-derivative term (in the project’s `(n+1)` indexing). -/
def eulerRatTerm (n : ℕ) (z : ℂ) : ℂ :=
  (2 * z) / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2)

/-- The finite partial sum of Euler’s rational terms. -/
def eulerRatPartialSum (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, eulerRatTerm n z

lemma eulerRatPartialSum_eq (N : ℕ) (z : ℂ) :
    eulerRatPartialSum N z
      =
    ∑ n ∈ Finset.range N, (2 * z) / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2) := by
  rfl

/-- A tiny normal-form lemma to avoid `2⁻¹*2⁻¹` vs `4⁻¹` mismatches. -/
lemma two_inv_mul_two_inv : ((2 : ℝ)⁻¹) * ((2 : ℝ)⁻¹) = (4 : ℝ)⁻¹ := by
  norm_num

/-!
## Summability on `nearZeroPunctured`
-/

/-- Phase 2A: pointwise norm bound for Euler’s rational term on `nearZeroPunctured`. -/
lemma norm_eulerRatTerm_le_of_mem_nearZeroPunctured {z : ℂ}
    (hz : z ∈ nearZeroPunctured) :
    ∀ n : ℕ, ‖eulerRatTerm n z‖ ≤ (8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖ := by
  classical
  rcases hz with ⟨hzBall, hz0⟩

  have hzlt : ‖z‖ < (1 / 2 : ℝ) := by
    simpa [nearZeroPunctured, Metric.mem_ball, dist_eq_norm] using hzBall
  have hzle : ‖z‖ ≤ (1 / 2 : ℝ) := le_of_lt hzlt

  -- Freeze the “quarter” bound once, in the `4⁻¹` normal form.
  have hz_sq_le : ‖z‖ ^ (2 : ℕ) ≤ ((4 : ℝ)⁻¹) := by
    have hz0' : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hmul : ‖z‖ * ‖z‖ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
      mul_le_mul hzle hzle hz0' (by norm_num)
    have : ‖z‖ ^ (2 : ℕ) ≤ ((2 : ℝ)⁻¹) * ((2 : ℝ)⁻¹) := by
      -- rewrite `1/2` as `2⁻¹`
      simpa [pow_two, one_div, div_eq_mul_inv, mul_assoc] using hmul
    simpa [two_inv_mul_two_inv] using this

  intro n

  -- Use `a = (n:ℂ) + 1` to match EulerRationalBounds’ lemmas.
  let a : ℂ := (n : ℂ) + 1

  have ha_ne : a ≠ 0 := by
    have ha' : a = ((n + 1 : ℕ) : ℂ) := by
      simp [a, Nat.cast_add, Nat.cast_one]
    simpa [ha'] using (show (((n + 1 : ℕ) : ℂ) ≠ 0) from by
      exact_mod_cast (Nat.succ_ne_zero n))

  have ha_norm : ‖a‖ = (n : ℝ) + 1 := by
    simpa [a] using norm_nat_add_one_complex n

  have ha_ge_one : (1 : ℝ) ≤ ‖a‖ := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
    rw [ha_norm]
    exact this

  have hnorm_z2 : ‖z ^ (2 : ℕ)‖ = ‖z‖ ^ (2 : ℕ) := by
    simp

  have hz2_le_quarter : ‖z ^ (2 : ℕ)‖ ≤ ((4 : ℝ)⁻¹) := by
    simpa [hnorm_z2] using hz_sq_le

  have ha2_ge_one : (1 : ℝ) ≤ ‖a ^ (2 : ℕ)‖ := by
    have ha0 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    have hmul : (1 : ℝ) ≤ ‖a‖ * ‖a‖ := by
      have : (1 : ℝ) * (1 : ℝ) ≤ ‖a‖ * ‖a‖ :=
        mul_le_mul ha_ge_one ha_ge_one (by norm_num) ha0
      simpa using this
    simpa [norm_pow, pow_two] using hmul

  have hz2_mul_le : ‖z ^ (2 : ℕ)‖ ≤ ((4 : ℝ)⁻¹) * ‖a ^ (2 : ℕ)‖ := by
    have : ((4 : ℝ)⁻¹) ≤ ((4 : ℝ)⁻¹) * ‖a ^ (2 : ℕ)‖ := by
      nlinarith [ha2_ge_one]
    exact le_trans hz2_le_quarter this

  have hsub :
      ‖a ^ (2 : ℕ)‖ - ‖z ^ (2 : ℕ)‖ ≤ ‖a ^ (2 : ℕ) - z ^ (2 : ℕ)‖ := by
    simpa using (norm_sub_norm_le (a ^ (2 : ℕ)) (z ^ (2 : ℕ)))

  have hswap :
      ‖a ^ (2 : ℕ) - z ^ (2 : ℕ)‖ = ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖ := by
    simpa using (norm_sub_rev (a ^ (2 : ℕ)) (z ^ (2 : ℕ)))

  have hden_lower :
      (3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖ ≤ ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖ := by
    have hlin :
        (3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖ ≤ ‖a ^ (2 : ℕ)‖ - ‖z ^ (2 : ℕ)‖ := by
      nlinarith [hz2_mul_le]
    have : (3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖ ≤ ‖a ^ (2 : ℕ) - z ^ (2 : ℕ)‖ :=
      le_trans hlin hsub
    simpa [hswap] using this

  have hpos_lb : (0 : ℝ) < (3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖ := by
    have h34 : (0 : ℝ) < (3 / 4 : ℝ) := by norm_num
    have ha2pos : (0 : ℝ) < ‖a ^ (2 : ℕ)‖ := by
      have : a ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 ha_ne
      exact norm_pos_iff.2 this
    exact mul_pos h34 ha2pos

  have hone_div :
      (1 : ℝ) / ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖ ≤ (1 : ℝ) / ((3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖) := by
    exact one_div_le_one_div_of_le hpos_lb hden_lower

  have hnorm_eq :
      ‖eulerRatTerm n z‖ = ‖(2 : ℂ) * z‖ / ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖ := by
    have ha2 : ((n + 1 : ℕ) : ℂ) ^ (2 : ℕ) = a ^ (2 : ℕ) := by
      simp [a, Nat.cast_add, Nat.cast_one]
    simp [eulerRatTerm, a]

  have hnorm_div_to_mul :
      ‖(2 : ℂ) * z‖ / ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖
          = ‖(2 : ℂ) * z‖ * ((1 : ℝ) / ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖) := by
    simp [div_eq_mul_inv]

  have hnorm_main :
      ‖eulerRatTerm n z‖ ≤ ‖(2 : ℂ) * z‖ * ((1 : ℝ) / ((3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖)) := by
    calc
      ‖eulerRatTerm n z‖
          = ‖(2 : ℂ) * z‖ / ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖ := hnorm_eq
      _   = ‖(2 : ℂ) * z‖ * ((1 : ℝ) / ‖z ^ (2 : ℕ) - a ^ (2 : ℕ)‖) := hnorm_div_to_mul
      _   ≤ ‖(2 : ℂ) * z‖ * ((1 : ℝ) / ((3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖)) := by
            exact mul_le_mul_of_nonneg_left hone_div (norm_nonneg ((2 : ℂ) * z))

  have hnorm_2z : ‖(2 : ℂ) * z‖ = (2 : ℝ) * ‖z‖ := by
    simp

  have hbasel_norm : ‖baselTerm n‖ = (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ) := by
    simpa using norm_baselTerm_natPow n

  have ha2_norm : ‖a ^ (2 : ℕ)‖ = ‖a‖ ^ (2 : ℕ) := by
    simp

  have ha2_ne : ‖a ^ (2 : ℕ)‖ ≠ 0 := by
    have : a ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 ha_ne
    exact (norm_ne_zero_iff).2 this

  have h34_ne : (3 / 4 : ℝ) ≠ 0 := by norm_num

  have hden_rewrite :
      (1 : ℝ) / ((3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖)
          = (4 / 3 : ℝ) * ((1 : ℝ) / ‖a ^ (2 : ℕ)‖) := by
    field_simp [h34_ne, ha2_ne]

  have hden_to_na :
      (1 : ℝ) / ‖a ^ (2 : ℕ)‖ = (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ) := by
    simp [ha2_norm, ha_norm]

  -- Finish.
  calc
    ‖eulerRatTerm n z‖
        ≤ ‖(2 : ℂ) * z‖ * ((1 : ℝ) / ((3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖)) := hnorm_main
    _   = ((2 : ℝ) * ‖z‖) * ((1 : ℝ) / ((3 / 4 : ℝ) * ‖a ^ (2 : ℕ)‖)) := by
          simp
    _   = ((2 : ℝ) * ‖z‖) * ((4 / 3 : ℝ) * ((1 : ℝ) / ‖a ^ (2 : ℕ)‖)) := by
          rw [hden_rewrite]
    _   = (8 / 3 : ℝ) * ‖z‖ * ((1 : ℝ) / ‖a ^ (2 : ℕ)‖) := by
          ring
    _   = (8 / 3 : ℝ) * ‖z‖ * ((1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
          rw [hden_to_na]
    _   = (8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖ := by
          simp [hbasel_norm, mul_assoc]

/-- Summability of the rational terms on `nearZeroPunctured`. -/
theorem summable_eulerRatTerm_of_mem_nearZeroPunctured {z : ℂ}
    (hz : z ∈ nearZeroPunctured) :
    Summable (fun n : ℕ => eulerRatTerm n z) := by
  classical

  -- Pointwise domination by a constant multiple of `‖baselTerm n‖`.
  have hbound :
      ∀ n : ℕ, ‖eulerRatTerm n z‖ ≤ (8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖ :=
    norm_eulerRatTerm_le_of_mem_nearZeroPunctured (z := z) hz

  -- Dominating series is summable by EulerRationalBounds.
  have hb : Summable (fun n : ℕ => (8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (summable_norm_baselTerm.mul_left ((8 / 3 : ℝ) * ‖z‖))

  have hnorm_summable : Summable (fun n : ℕ => ‖eulerRatTerm n z‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hb
    exact hbound n

  -- Summability from summable norms.
  exact Summable.of_norm hnorm_summable

/-- The partial sums converge to the `tsum` (standard). -/
theorem tendsto_eulerRatPartialSum_tsum {z : ℂ} (hz : z ∈ nearZeroPunctured) :
    Tendsto (fun N : ℕ => eulerRatPartialSum N z) atTop
      (nhds (∑' n : ℕ, eulerRatTerm n z)) := by
  simpa [eulerRatPartialSum] using
    (summable_eulerRatTerm_of_mem_nearZeroPunctured (z := z) hz).hasSum.tendsto_sum_nat

/-!
## Identify the log-derivative as a tsum
-/

/-- `logDeriv eulerLimitFun z` equals the `tsum` of Euler’s rational terms, on `nearZeroPunctured`. -/
theorem logDeriv_eulerLimitFun_eq_tsum_eulerRatTerm {z : ℂ}
    (hz : z ∈ nearZeroPunctured) :
    logDeriv eulerLimitFun z = ∑' n : ℕ, eulerRatTerm n z := by
  have h1 :
      Tendsto (fun N =>
        ∑ i ∈ Finset.range N, (2 * z) / (z ^ 2 - ((i + 1 : ℕ) : ℂ) ^ 2))
        atTop
        (nhds (logDeriv eulerLimitFun z)) :=
    tendsto_eulerRationalSum (z := z) hz

  have h1' :
      Tendsto (fun N : ℕ => eulerRatPartialSum N z) atTop (nhds (logDeriv eulerLimitFun z)) := by
    simpa [eulerRatPartialSum, eulerRatTerm] using h1

  have h2 :
      Tendsto (fun N : ℕ => eulerRatPartialSum N z) atTop
        (nhds (∑' n : ℕ, eulerRatTerm n z)) :=
    tendsto_eulerRatPartialSum_tsum (z := z) hz

  exact tendsto_nhds_unique h1' h2

end

end EulerBasel



