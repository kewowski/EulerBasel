/-
EulerBasel/CoefficientProductSide_Phase2C.lean

Phase 2C: log-derivative linear behaviour on the punctured neighbourhood.

Main theorem exported:
  logDeriv_eulerLimitFun_add_two_baselSum_mul_isLittleO_punctured
-/

import EulerBasel.CoefficientDefs
import EulerBasel.CoefficientEulerRationalTsum
import EulerBasel.EulerRationalBounds
import EulerBasel.TopologyPunctured
import EulerBasel.CoefficientEulerLicensing  -- mem_nearZeroPunctured_iff

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.Tannery

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics

namespace EulerBasel

noncomputable section

/-- Eventually near `0`, we lie in the ball `Metric.ball 0 (1/2)`. -/
private lemma eventually_mem_ball_half :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) := by
  exact Metric.ball_mem_nhds (0 : ℂ) (by norm_num)

/-- Eventually on the punctured neighbourhood, `z ∈ nearZeroPunctured`. -/
private lemma eventually_mem_nearZeroPunctured_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured := by
  classical
  have hball :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) := by
    exact (eventually_mem_ball_half).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
    EulerBasel.eventually_ne_zero_punctured
  filter_upwards [hball, hne] with z hzBall hz0

  have hdist : dist z (0 : ℂ) < (1 / 2 : ℝ) :=
    Metric.mem_ball.mp hzBall

  have hzlt : ‖z‖ < (1 / 2 : ℝ) := by
    have : ‖z - 0‖ < (1 / 2 : ℝ) := by
      simpa [dist_eq_norm] using hdist
    simpa using (by simpa using this)

  exact (mem_nearZeroPunctured_iff (z := z)).2 ⟨hzlt, hz0⟩

/-- Per-term correction after dividing by `z`. -/
def tTerm (n : ℕ) (z : ℂ) : ℂ :=
  eulerRatTerm n z / z + (2 : ℂ) * baselTerm n

/-- Uniform bound for `‖eulerRatTerm n z / z‖` on `nearZeroPunctured`. -/
lemma norm_eulerRatTerm_div_z_le (n : ℕ) {z : ℂ} (hz : z ∈ nearZeroPunctured) :
    ‖eulerRatTerm n z / z‖ ≤ (8 / 3 : ℝ) * ‖baselTerm n‖ := by
  have hz0 : z ≠ 0 := (mem_nearZeroPunctured_iff (z := z)).1 hz |>.2
  have hzpos : 0 < ‖z‖ := by
    simpa [norm_eq_zero] using hz0

  have hRat :
      ‖eulerRatTerm n z‖ ≤ (8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖ :=
    (norm_eulerRatTerm_le_of_mem_nearZeroPunctured (z := z) hz) n

  have hnormdiv : ‖eulerRatTerm n z / z‖ = ‖eulerRatTerm n z‖ / ‖z‖ := by
    simp

  have hDiv0 :
      ‖eulerRatTerm n z‖ / ‖z‖ ≤ ((8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖) / ‖z‖ := by
    exact div_le_div_of_nonneg_right hRat (le_of_lt hzpos)

  have hR :
      ((8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖) / ‖z‖ = (8 / 3 : ℝ) * ‖baselTerm n‖ := by
    field_simp [hzpos.ne']

  calc
    ‖eulerRatTerm n z / z‖
        = ‖eulerRatTerm n z‖ / ‖z‖ := hnormdiv
    _   ≤ ((8 / 3 : ℝ) * ‖z‖ * ‖baselTerm n‖) / ‖z‖ := hDiv0
    _   = (8 / 3 : ℝ) * ‖baselTerm n‖ := hR

/-- A REAL-valued domination sequence for Tannery. -/
def bR (n : ℕ) : ℝ :=
  (14 / 3 : ℝ) * ‖baselTerm n‖

lemma summable_bR : Summable bR := by
  change Summable (fun n : ℕ => (14 / 3 : ℝ) * ‖baselTerm n‖)
  exact (summable_norm_baselTerm.mul_left (14 / 3 : ℝ))

lemma eventually_norm_tTerm_le_bR :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ∀ n : ℕ, ‖tTerm n z‖ ≤ bR n := by
  classical
  have hmem : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured :=
    eventually_mem_nearZeroPunctured_punctured
  filter_upwards [hmem] with z hz
  intro n

  have hA : ‖eulerRatTerm n z / z‖ ≤ (8 / 3 : ℝ) * ‖baselTerm n‖ :=
    norm_eulerRatTerm_div_z_le (n := n) (z := z) hz

  have hB : ‖(2 : ℂ) * baselTerm n‖ = (2 : ℝ) * ‖baselTerm n‖ := by
    simp

  have htri := norm_add_le (eulerRatTerm n z / z) ((2 : ℂ) * baselTerm n)

  have hstep :
      ‖tTerm n z‖ ≤ (8 / 3 : ℝ) * ‖baselTerm n‖ + (2 : ℝ) * ‖baselTerm n‖ := by
    have : ‖eulerRatTerm n z / z‖ + ‖(2 : ℂ) * baselTerm n‖
            ≤ (8 / 3 : ℝ) * ‖baselTerm n‖ + (2 : ℝ) * ‖baselTerm n‖ := by
      exact add_le_add hA (by simp)
    have htri' : ‖tTerm n z‖ ≤ ‖eulerRatTerm n z / z‖ + ‖(2 : ℂ) * baselTerm n‖ := by
      simpa [tTerm] using htri
    exact le_trans htri' this

  have hconst : (8 / 3 : ℝ) + 2 = (14 / 3 : ℝ) := by norm_num

  have hfinal : ‖tTerm n z‖ ≤ (14 / 3 : ℝ) * ‖baselTerm n‖ := by
    calc
      ‖tTerm n z‖
          ≤ (8 / 3 : ℝ) * ‖baselTerm n‖ + (2 : ℝ) * ‖baselTerm n‖ := hstep
      _ = ((8 / 3 : ℝ) + 2) * ‖baselTerm n‖ := by ring
      _ = (14 / 3 : ℝ) * ‖baselTerm n‖ := by simp [hconst]

  simpa [bR] using hfinal

/-- Stable algebra: `(A + B*z)/z = A/z + B` when `z ≠ 0`. -/
lemma add_mul_div_eq_div_add {A B z : ℂ} (hz : z ≠ 0) :
    (A + B * z) / z = A / z + B := by
  field_simp [hz]

/--
Phase 2C main statement.
-/
theorem logDeriv_eulerLimitFun_add_two_baselSum_mul_isLittleO_punctured :
    (fun z : ℂ => logDeriv eulerLimitFun z + (2 * baselSum) * z)
      =o[𝓝[≠] (0 : ℂ)] (fun z : ℂ => z) := by
  classical

  have hgf :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        (fun z : ℂ => z) z = 0 →
          (fun z : ℂ => logDeriv eulerLimitFun z + (2 * baselSum) * z) z = 0 := by
    have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
      EulerBasel.eventually_ne_zero_punctured
    filter_upwards [hne] with z hz
    intro hz0
    exact (hz hz0).elim

  refine
    (Asymptotics.isLittleO_iff_tendsto'
      (f := fun z : ℂ => logDeriv eulerLimitFun z + (2 * baselSum) * z)
      (g := fun z : ℂ => z)
      (l := 𝓝[≠] (0 : ℂ)) hgf).2 ?_

  let q : ℂ → ℂ := fun z => (logDeriv eulerLimitFun z + (2 * baselSum) * z) / z

  have hmem : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured :=
    eventually_mem_nearZeroPunctured_punctured

  have hq_tsum :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), q z = ∑' (n : ℕ), tTerm n z := by
    filter_upwards [hmem] with z hz
    have hz0 : z ≠ 0 := (mem_nearZeroPunctured_iff (z := z)).1 hz |>.2

    have hlog : logDeriv eulerLimitFun z = ∑' (n : ℕ), eulerRatTerm n z :=
      logDeriv_eulerLimitFun_eq_tsum_eulerRatTerm (z := z) hz

    have hsRat : Summable fun n : ℕ => eulerRatTerm n z :=
      summable_eulerRatTerm_of_mem_nearZeroPunctured (z := z) hz
    have hsBas : Summable fun n : ℕ => baselTerm n :=
      summable_baselTerm

    have hsumScaled :
        HasSum (fun n : ℕ => eulerRatTerm n z / z)
          ((∑' n : ℕ, eulerRatTerm n z) / z) := by
      have h :
          HasSum (fun n : ℕ => eulerRatTerm n z) (∑' n : ℕ, eulerRatTerm n z) :=
        hsRat.hasSum
      have h' :
          HasSum (fun n : ℕ => eulerRatTerm n z * z⁻¹)
            ((∑' n : ℕ, eulerRatTerm n z) * z⁻¹) :=
        h.mul_right (z⁻¹)
      simpa [div_eq_mul_inv, mul_assoc] using h'

    have hsumBas :
        HasSum (fun n : ℕ => (2 : ℂ) * baselTerm n)
          ((2 : ℂ) * (∑' n : ℕ, baselTerm n)) := by
      have h :
          HasSum (fun n : ℕ => baselTerm n) (∑' n : ℕ, baselTerm n) :=
        hsBas.hasSum
      simpa [mul_assoc] using h.mul_left (2 : ℂ)

    have hsumAll :
        HasSum
          (fun n : ℕ => (eulerRatTerm n z / z) + (2 : ℂ) * baselTerm n)
          (((∑' n : ℕ, eulerRatTerm n z) / z) + (2 : ℂ) * (∑' n : ℕ, baselTerm n)) :=
      hsumScaled.add hsumBas

    have htsum :
        (∑' n : ℕ, ((eulerRatTerm n z / z) + (2 : ℂ) * baselTerm n))
          =
        ((∑' n : ℕ, eulerRatTerm n z) / z) + (2 : ℂ) * (∑' n : ℕ, baselTerm n) :=
      hsumAll.tsum_eq

    have hq' :
        q z =
          ((∑' n : ℕ, eulerRatTerm n z) / z) + (2 : ℂ) * (∑' n : ℕ, baselTerm n) := by
      have hdiv :
          (logDeriv eulerLimitFun z + (2 * baselSum) * z) / z
            =
          (logDeriv eulerLimitFun z) / z + (2 * baselSum) := by
        simpa [mul_assoc] using
          (add_mul_div_eq_div_add
            (A := logDeriv eulerLimitFun z) (B := (2 * baselSum)) (z := z) hz0)
      calc
        q z
            = (logDeriv eulerLimitFun z + (2 * baselSum) * z) / z := by rfl
        _   = (logDeriv eulerLimitFun z) / z + (2 * baselSum) := hdiv
        _   = (∑' n : ℕ, eulerRatTerm n z) / z + (2 * baselSum) := by
              simp [hlog]
        _   = (∑' n : ℕ, eulerRatTerm n z) / z + (2 : ℂ) * baselSum := by ring
        _   = (∑' n : ℕ, eulerRatTerm n z) / z + (2 : ℂ) * (∑' n : ℕ, baselTerm n) := by
              simp [baselSum]

    calc
      q z
          = ((∑' n : ℕ, eulerRatTerm n z) / z) + (2 : ℂ) * (∑' n : ℕ, baselTerm n) := hq'
      _   = (∑' n : ℕ, ((eulerRatTerm n z / z) + (2 : ℂ) * baselTerm n)) := by
              exact htsum.symm
      _   = ∑' n : ℕ, tTerm n z := by
              simp [tTerm]

  have htTerm_tendsto0 (n : ℕ) :
      Tendsto (fun z : ℂ => tTerm n z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    let a : ℂ := (((n + 1 : ℕ) : ℂ) ^ (2 : ℕ))

    have ha_ne : a ≠ 0 := by
      have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      exact pow_ne_zero 2 hn1

    let F : ℂ → ℂ := fun z =>
      (2 : ℂ) / (z ^ (2 : ℕ) - a) + (2 : ℂ) / a

    have hden0 : (0 : ℂ) ^ (2 : ℕ) - a ≠ 0 := by
      simpa [a] using sub_ne_zero.mpr ha_ne

    have hF0 : F (0 : ℂ) = (0 : ℂ) := by
      have hden0' : (0 : ℂ) - a ≠ 0 := by
        simpa using sub_ne_zero.mpr ha_ne
      have : (2 : ℂ) / ((0 : ℂ) ^ (2 : ℕ) - a) + (2 : ℂ) / a = (0 : ℂ) := by
        field_simp [ha_ne, hden0', a] ; ring
      simpa [F] using this

    have hcont : ContinuousAt F (0 : ℂ) := by
      have h1 : ContinuousAt (fun z : ℂ => (2 : ℂ) / (z ^ (2 : ℕ) - a)) (0 : ℂ) := by
        have hden_cont : ContinuousAt (fun z : ℂ => z ^ (2 : ℕ) - a) (0 : ℂ) := by
          simpa using ((continuous_pow 2).continuousAt.sub continuousAt_const)
        simpa [div_eq_mul_inv] using (continuousAt_const.mul (hden_cont.inv₀ hden0))
      have h2 : ContinuousAt (fun _z : ℂ => (2 : ℂ) / a) (0 : ℂ) := by
        simpa [div_eq_mul_inv] using
          (continuousAt_const : ContinuousAt (fun _z : ℂ => (2 : ℂ) / a) (0 : ℂ))
      simpa [F] using h1.add h2

    have hF_tendsto :
        Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      have : Tendsto F (𝓝 (0 : ℂ)) (𝓝 (F (0 : ℂ))) := hcont.tendsto
      have : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (F (0 : ℂ))) := this.mono_left nhdsWithin_le_nhds
      simpa [hF0] using this

    have a_eq : a = ((n : ℂ) + 1) ^ (2 : ℕ) := by
      simp [a, Nat.cast_add, Nat.cast_one]

    have hb : (2 : ℂ) * baselTerm n = (2 : ℂ) / a := by
      unfold baselTerm
      simp [a_eq, div_eq_mul_inv]

    have hEq : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), tTerm n z = F z := by
      filter_upwards [EulerBasel.eventually_ne_zero_punctured] with z hz0
      have hcancel : eulerRatTerm n z / z = (2 : ℂ) / (z ^ (2 : ℕ) - a) := by
        unfold eulerRatTerm
        field_simp [hz0, a]; ring
      calc
        tTerm n z
            = eulerRatTerm n z / z + (2 : ℂ) * baselTerm n := by rfl
        _   = (2 : ℂ) / (z ^ (2 : ℕ) - a) + (2 : ℂ) * baselTerm n := by
              simp [hcancel]
        _   = (2 : ℂ) / (z ^ (2 : ℕ) - a) + (2 : ℂ) / a := by
              simp [hb]
        _   = F z := by
              rfl

    exact (tendsto_congr' hEq).2 hF_tendsto

  have htend_tsum :
      Tendsto (fun z : ℂ => ∑' (n : ℕ), tTerm n z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h :=
      tendsto_tsum_of_dominated_convergence
        (α := ℂ) (β := ℕ) (G := ℂ) (𝓕 := 𝓝[≠] (0 : ℂ))
        (f := fun z n => tTerm n z)
        (g := fun (_ : ℕ) => (0 : ℂ))
        (bound := bR)
        summable_bR
        (hab := fun n => htTerm_tendsto0 n)
        (h_bound := eventually_norm_tTerm_le_bR)
    simpa using h

  have htend_q : Tendsto q (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    refine (tendsto_congr' ?_).2 htend_tsum
    exact hq_tsum

  simpa [q] using htend_q

end

end EulerBasel


