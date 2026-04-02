import EulerBasel.TopologyPunctured
import EulerBasel.SegmentIntegralPunctured
import EulerBasel.WeightedSegmentIntegral
import EulerBasel.LogFTC
import EulerBasel.NearZeroSegment
import EulerBasel.QuadraticReconstruction_FTC

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Topology BigOperators Asymptotics Interval
open Filter Asymptotics
open Set

namespace EulerBasel
noncomputable section

/-!
EulerBasel/QuadraticReconstruction_StepD.lean

Step D capstone for QuadraticReconstruction.lean.
-/

/--
Step D (standalone).

Conclude:
  (eulerLimitFun0 z - (1 - b*z^2)) / z^2 → 0   on `𝓝[≠] 0`.
-/
lemma tendsto_quadratic_remainder_div_stepD
    (b : ℂ)
    (eulerLimitFun0 : ℂ → ℂ)
    (H0 Hfun g : ℂ → ℂ)
    (hH0_def : ∀ z : ℂ, H0 z = eulerLimitFun0 z * NormedSpace.exp (b * z ^ 2))
    (hH0_eq_Hfun : ∀ {z : ℂ}, z ≠ 0 → H0 z = Hfun z)
    (hcoreWeighted :
      ∀ᶠ z in 𝓝[≠]0,
        Hfun z - (1 : ℂ) =
          (z ^ 2) * ∫ s in (0 : ℝ)..1, (s : ℂ) * g ((s : ℂ) * z))
    (hI :
      Tendsto (fun z : ℂ => ∫ s in (0 : ℝ)..1, (s : ℂ) * g ((s : ℂ) * z))
        (𝓝[≠]0) (𝓝 (0 : ℂ))) :
    Tendsto (fun z : ℂ =>
        (eulerLimitFun0 z - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2))
      (𝓝[≠]0) (𝓝 (0 : ℂ)) := by
  classical

  -- Integral I(z).
  let I : ℂ → ℂ := fun z =>
    ∫ s in (0 : ℝ)..1, (s : ℂ) * g ((s : ℂ) * z)

  have hI' : Tendsto I (𝓝[≠]0) (𝓝 (0 : ℂ)) := by
    simpa [I] using hI

  -- Nonzero on punctured.
  have hne : ∀ᶠ z in (𝓝[≠]0 : Filter ℂ), z ≠ 0 :=
    EulerBasel.eventually_ne_zero_punctured

  -- From the core identity: (Hfun z - 1)/z^2 = I z eventually.
  have hquot_Hfun :
      (fun z : ℂ => (Hfun z - (1 : ℂ)) / (z ^ 2)) =ᶠ[𝓝[≠]0] I := by
    filter_upwards [hcoreWeighted, hne] with z hz hzn
    have hz2 : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hzn
    calc
      (Hfun z - (1 : ℂ)) / (z ^ 2)
          = ((z ^ 2) * I z) / (z ^ 2) := by
              rw [hz]
      _ = I z := by
          have : ((z ^ 2) * I z) / (z ^ 2) = I z := by
            field_simp [hz2]
          simpa using this

  have hT_Hfun :
      Tendsto (fun z : ℂ => (Hfun z - (1 : ℂ)) / (z ^ 2)) (𝓝[≠]0) (𝓝 (0 : ℂ)) :=
    hI'.congr' hquot_Hfun.symm

  -- Replace Hfun with H0 on punctured.
  have hquot_H0_Hfun :
      (fun z : ℂ => (H0 z - (1 : ℂ)) / (z ^ 2))
        =ᶠ[𝓝[≠]0] (fun z : ℂ => (Hfun z - (1 : ℂ)) / (z ^ 2)) := by
    filter_upwards [hne] with z hzn
    have : H0 z = Hfun z := hH0_eq_Hfun (z := z) hzn
    simp [this]

  have hT_H0 :
      Tendsto (fun z : ℂ => (H0 z - (1 : ℂ)) / (z ^ 2)) (𝓝[≠]0) (𝓝 (0 : ℂ)) :=
    hT_Hfun.congr' hquot_H0_Hfun.symm

  -- Rewrite eulerLimitFun0 using H0 and exp(-b z^2).
  have hRewrite :
      ∀ z : ℂ, eulerLimitFun0 z = H0 z * NormedSpace.exp (-(b * z ^ 2)) := by
    intro z
    have hmul :
        NormedSpace.exp (b * z ^ 2) * NormedSpace.exp (-(b * z ^ 2)) = (1 : ℂ) := by
      have hx : NormedSpace.exp (b * z ^ 2) ≠ (0 : ℂ) := by
        simpa [Complex.exp_eq_exp_ℂ] using (Complex.exp_ne_zero (b * z ^ 2))
      calc
        NormedSpace.exp (b * z ^ 2) * NormedSpace.exp (-(b * z ^ 2))
            = NormedSpace.exp (b * z ^ 2) * (NormedSpace.exp (b * z ^ 2))⁻¹ := by
                simp [NormedSpace.exp_neg]
        _ = (1 : ℂ) := by
                simp [hx]

    calc
      eulerLimitFun0 z
          = (eulerLimitFun0 z) * (1 : ℂ) := by simp
      _ = (eulerLimitFun0 z) * (NormedSpace.exp (b * z ^ 2) * NormedSpace.exp (-(b * z ^ 2))) := by
            simp [hmul]
      _ = (eulerLimitFun0 z * NormedSpace.exp (b * z ^ 2)) * NormedSpace.exp (-(b * z ^ 2)) := by
            simp [mul_assoc]
      _ = H0 z * NormedSpace.exp (-(b * z ^ 2)) := by
            simp [hH0_def z, mul_assoc]

  /- ### Exponential remainder at 0 -/

  -- x(z) := -(b*z^2) → 0
  have hx_tendsto :
      Tendsto (fun z : ℂ => -(b * z ^ 2)) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hz2 : Tendsto (fun z : ℂ => z ^ 2) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 0) (𝓝 0)).pow 2)
    have hbz2 : Tendsto (fun z : ℂ => b * z ^ 2) (𝓝 (0 : ℂ)) (𝓝 (b * (0 : ℂ))) :=
      (tendsto_const_nhds.mul hz2)
    have hbz2' : Tendsto (fun z : ℂ => b * z ^ 2) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using hbz2
    simpa using hbz2'.neg

  -- Eventually, ‖x(z)‖ ≤ 1.
  have hxsmall : ∀ᶠ z in (𝓝 (0 : ℂ)), ‖-(b * z ^ 2)‖ ≤ (1 : ℝ) := by
    have hnorm0 :
        Tendsto (fun z : ℂ => ‖-(b * z ^ 2)‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) :=
      (tendsto_norm_zero.comp hx_tendsto)
    have hlt : ∀ᶠ z in (𝓝 (0 : ℂ)), ‖-(b * z ^ 2)‖ < (1 : ℝ) := by
      have hmem : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := by
        simpa using (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      exact hnorm0.eventually hmem
    exact hlt.mono (fun _ hz => le_of_lt hz)

  have hT_exp_remainder0 :
      Tendsto
        (fun z : ℂ =>
          (NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2))
        (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    -- bound the norm by ‖b‖^2 * ‖z‖^2
    have hbound :
        ∀ᶠ z in (𝓝 (0 : ℂ)),
          ‖(NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2)‖
            ≤ (‖b‖ ^ 2) * (‖z‖ ^ 2) := by
      filter_upwards [hxsmall] with z hz1
      by_cases hz0 : z = 0
      · simp [hz0]
      ·
        have hnume :
            NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)
              = NormedSpace.exp (-(b * z ^ 2)) - (1 : ℂ) - (-(b * z ^ 2)) := by
          ring_nf

        have hlem :
            ‖NormedSpace.exp (-(b * z ^ 2)) - (1 : ℂ) - (-(b * z ^ 2))‖
              ≤ ‖-(b * z ^ 2)‖ ^ 2 := by
          simpa [Complex.exp_eq_exp_ℂ] using
            (Complex.norm_exp_sub_one_sub_id_le (x := (-(b * z ^ 2))) hz1)

        have hdivineq :
            ‖(NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2)‖
              ≤ (‖-(b * z ^ 2)‖ ^ 2) / ‖(z ^ 2 : ℂ)‖ := by
          have :=
            div_le_div_of_nonneg_right (by simpa [hnume] using hlem) (norm_nonneg (z ^ 2 : ℂ))
          simpa [hnume, norm_div] using this

        have hzNorm : (‖z‖ : ℝ) ≠ 0 := by
          intro h
          apply hz0
          exact norm_eq_zero.mp h

        have hzNorm2 : (‖z‖ ^ 2 : ℝ) ≠ 0 := by
          exact pow_ne_zero 2 hzNorm

        have hz2norm : ‖(z ^ 2 : ℂ)‖ = ‖z‖ ^ 2 := by
          -- important: one-shot proof, no extra tactic after it (prevents “no goals”)
          simp [pow_two]

        have hR :
            (‖-(b * z ^ 2)‖ ^ 2) / ‖(z ^ 2 : ℂ)‖ = (‖b‖ ^ 2) * (‖z‖ ^ 2) := by
          have hn : (‖-(b * z ^ 2)‖ : ℝ) = ‖b‖ * ‖z‖ ^ 2 := by
            simp [pow_two]
          have hscalar :
              ((‖b‖ * ‖z‖ ^ 2) ^ 2) / (‖z‖ ^ 2) = (‖b‖ ^ 2) * (‖z‖ ^ 2) := by
            field_simp [hzNorm2]
            
          simpa [hn, hz2norm, pow_two] using hscalar

        exact le_trans hdivineq (le_of_eq hR)

    have hR_tendsto :
        Tendsto (fun z : ℂ => (‖b‖ ^ 2 : ℝ) * (‖z‖ ^ 2)) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
      have hz : Tendsto (fun z : ℂ => ‖z‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := tendsto_norm_zero
      have hz2 : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
        simpa using (hz.pow 2)
      simpa using (tendsto_const_nhds.mul hz2)

    have hnorm_tendsto :
        Tendsto
          (fun z : ℂ =>
            ‖(NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2)‖)
          (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
      refine (Filter.Tendsto.squeeze'
        (f := fun z : ℂ =>
          ‖(NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2)‖)
        (g := fun _ : ℂ => (0 : ℝ))
        (h := fun z : ℂ => (‖b‖ ^ 2 : ℝ) * (‖z‖ ^ 2))
        (a := (0 : ℝ))
        (hg := tendsto_const_nhds)
        (hh := hR_tendsto)
        ?_ ?_)
      · exact Filter.Eventually.of_forall (fun z => norm_nonneg _)
      · exact hbound

    exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_tendsto

  have hT_exp_remainder :
      Tendsto
        (fun z : ℂ =>
          (NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2))
        (𝓝[≠]0) (𝓝 (0 : ℂ)) :=
    hT_exp_remainder0.mono_left nhdsWithin_le_nhds

  -- exp(-b z^2) → 1 at 0
  have hT_exp0 :
      Tendsto (fun z : ℂ => NormedSpace.exp (-(b * z ^ 2))) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hcont :
        Tendsto (fun z : ℂ => Complex.exp (-(b * z ^ 2))) (𝓝 (0 : ℂ)) (𝓝 (Complex.exp (0 : ℂ))) :=
      (Complex.continuous_exp.tendsto (0 : ℂ)).comp hx_tendsto
    simpa [Complex.exp_eq_exp_ℂ] using hcont

  have hT_exp :
      Tendsto (fun z : ℂ => NormedSpace.exp (-(b * z ^ 2))) (𝓝[≠]0) (𝓝 (1 : ℂ)) :=
    hT_exp0.mono_left nhdsWithin_le_nhds

  -- Final algebra: split remainder.
  have hMainEq :
      (fun z : ℂ =>
          (eulerLimitFun0 z - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2))
        =ᶠ[𝓝[≠]0]
      (fun z : ℂ =>
          ((H0 z - (1 : ℂ)) / (z ^ 2)) * NormedSpace.exp (-(b * z ^ 2))
            + (NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2)) := by
    filter_upwards [hne] with z hzn
    have he : eulerLimitFun0 z = H0 z * NormedSpace.exp (-(b * z ^ 2)) := hRewrite z
    have hz2 : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hzn

    -- clear the denominator; reduce to a clean numerator identity and solve it directly
    field_simp [hz2]

    -- goal is now a numerator identity; rewrite eulerLimitFun0 using `he` and finish by commutativity + ring_nf
    
    have :
        -1 + eulerLimitFun0 z + b * z ^ 2 =
          -1 + b * z ^ 2 + H0 z * NormedSpace.exp (-(b * z ^ 2)) := by
      simp [he, add_assoc, add_left_comm, add_comm]
    
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, this, he] using (by
      -- `ring_nf` normalises the remaining additive/multiplicative structure
      ring_nf)

  have hT_first :
      Tendsto
        (fun z : ℂ =>
          ((H0 z - (1 : ℂ)) / (z ^ 2)) * NormedSpace.exp (-(b * z ^ 2)))
        (𝓝[≠]0) (𝓝 (0 : ℂ)) := by
    simpa using (hT_H0.mul hT_exp)

  have hT_sum :
      Tendsto
        (fun z : ℂ =>
          ((H0 z - (1 : ℂ)) / (z ^ 2)) * NormedSpace.exp (-(b * z ^ 2))
            + (NormedSpace.exp (-(b * z ^ 2)) - ((1 : ℂ) - b * z ^ 2)) / (z ^ 2))
        (𝓝[≠]0) (𝓝 (0 : ℂ)) := by
    simpa using (hT_first.add hT_exp_remainder)

  exact hT_sum.congr' hMainEq.symm

end

end EulerBasel

