/-
EulerBasel/DerivHMulZ.lean

Provide the Step C integrability hypothesis (eventually in z):

  IntervalIntegrable (fun s => deriv (H b F) ((s:ℂ)*z) * z) volume 0 1

Packaged as an `∀ᶠ z in 𝓝[≠]0, ...` lemma.

Design:
- NO continuity of logDeriv (mathlib does not provide a stable lemma for it here).
- Measurability comes from `measurable_deriv` + measurability of `s ↦ (s:ℂ)*z`.
- Boundedness comes from `deriv_H_eq` + eventual bounds on H and r near 0.
-/

import EulerBasel.StepC_IntegrableIoc
import EulerBasel.LogFTC
import EulerBasel.NearZeroSegment

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Topology Interval
open Filter
open MeasureTheory

namespace EulerBasel
noncomputable section

theorem eventually_hint_derivH_mul_z
    (b : ℂ) (F : ℂ → ℂ)
    (hnear : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured)
    (hFdiff : ∀ {w : ℂ}, w ∈ nearZeroPunctured → DifferentiableAt ℂ F w)
    (hFne   : ∀ {w : ℂ}, w ∈ nearZeroPunctured → F w ≠ 0)
    (hHfun : Tendsto (H (b := b) (F := F)) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)))
    (hr : Tendsto (r (b := b) (F := F)) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ))) :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      IntervalIntegrable
        (fun s : ℝ => (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
        MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  classical

  --------------------------------------------------------------------
  -- Eventual bounds on H and r near 0 (punctured).
  --------------------------------------------------------------------

  have hHbd : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), ‖H (b := b) (F := F) w‖ ≤ (2 : ℝ) := by
    have hball : Metric.ball (1 : ℂ) (1 : ℝ) ∈ 𝓝 (1 : ℂ) := by
      exact Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < (1 : ℝ))
    have hle : ∀ᶠ y : ℂ in 𝓝 (1 : ℂ), ‖y‖ ≤ (2 : ℝ) := by
      filter_upwards [hball] with y hy
      have hy' : ‖y - (1 : ℂ)‖ ≤ (1 : ℝ) := by
        have : ‖y - (1 : ℂ)‖ < (1 : ℝ) := by
          simpa [Metric.mem_ball, dist_eq_norm] using hy
        exact le_of_lt this
      have : ‖y‖ ≤ ‖y - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
        simpa [sub_eq_add_neg, add_assoc] using
          (norm_add_le (y - (1 : ℂ)) (1 : ℂ))
      have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
      calc
        ‖y‖ ≤ ‖y - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := this
        _   ≤ (1 : ℝ) + (1 : ℝ) := by
          have h1le : ‖(1 : ℂ)‖ ≤ (1 : ℝ) := by
            simp
          simpa [h1] using add_le_add hy' h1le
        _   = (2 : ℝ) := by norm_num
    exact (hHfun.eventually hle)

  have hrbd : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), ‖r (b := b) (F := F) w‖ ≤ (1 : ℝ) := by
    have hmem : Metric.ball (0 : ℂ) (1 : ℝ) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < (1 : ℝ))
    have hle : ∀ᶠ y : ℂ in 𝓝 (0 : ℂ), ‖y‖ ≤ (1 : ℝ) := by
      filter_upwards [hmem] with y hy
      have : ‖y‖ < (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      exact le_of_lt this
    exact (hr.eventually hle)

  --------------------------------------------------------------------
  -- Pick a small ball around 0 inside the intersection set where both bounds hold.
  --------------------------------------------------------------------

  have hUmem :
      ({w : ℂ | ‖H (b := b) (F := F) w‖ ≤ (2 : ℝ)} ∩
       {w : ℂ | ‖r (b := b) (F := F) w‖ ≤ (1 : ℝ)})
        ∈ 𝓝[≠] (0 : ℂ) := by
    exact Filter.inter_mem hHbd hrbd

  rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hUmem) with ⟨V, hV0, hVsub⟩
  rcases Metric.mem_nhds_iff.1 hV0 with ⟨ε, hεpos, hεsub⟩
  have hsmall : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ < ε := by
    have hball0 : Metric.ball (0 : ℂ) ε ∈ 𝓝 (0 : ℂ) := by
      exact Metric.ball_mem_nhds (0 : ℂ) hεpos
    have hnorm0 : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ‖z‖ < ε := by
      filter_upwards [hball0] with z hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hnorm0

  --------------------------------------------------------------------
  -- Now work pointwise in z (eventually).
  --------------------------------------------------------------------

  filter_upwards [hnear, hsmall] with z hz hznorm

  -- Define the integrand u(s) = deriv(H)( (s:ℂ)*z ) * z.
  let u : ℝ → ℂ :=
    fun s : ℝ => (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z

  --------------------------------------------------------------------
  -- AE-strong measurability of u on Ioc(0,1] under volume.restrict.
  --------------------------------------------------------------------

  have u_mble :
      MeasureTheory.AEStronglyMeasurable u
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hder_mble : Measurable (deriv (H (b := b) (F := F))) := by
      simpa using (measurable_deriv (H (b := b) (F := F)))
    have hseg_mble : Measurable (fun s : ℝ => ((s : ℂ) * z)) := by
      exact ((Complex.continuous_ofReal).mul continuous_const).measurable
    have hcomp_mble : Measurable (fun s : ℝ => deriv (H (b := b) (F := F)) ((s : ℂ) * z)) :=
      hder_mble.comp hseg_mble
    have : MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => deriv (H (b := b) (F := F)) ((s : ℂ) * z))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      exact hcomp_mble.aestronglyMeasurable
    simpa [u] using this.mul_const z

  --------------------------------------------------------------------
  -- Pointwise bounds on u on Ioc(0,1] using the chosen small ball and `deriv_H_eq`.
  --------------------------------------------------------------------

  have hbound :
      ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖u s‖ ≤ (2 : ℝ) * ‖z‖ * (1 : ℝ) * (1 : ℝ) * ‖z‖ := by
    intro s hs
    have hseg : ((s : ℂ) * z) ∈ nearZeroPunctured :=
      segMul_mem_nearZeroPunctured (z := z) hz hs
    have hwsz : (s : ℂ) * z ≠ 0 :=
      (mem_nearZeroPunctured_iff (z := (s : ℂ) * z)).1 hseg |>.2
    have hF_at : DifferentiableAt ℂ F ((s : ℂ) * z) := hFdiff (w := (s : ℂ) * z) hseg
    have hF0_at : F ((s : ℂ) * z) ≠ 0 := hFne (w := (s : ℂ) * z) hseg

    have hder :
        deriv (H (b := b) (F := F)) ((s : ℂ) * z)
          = (H (b := b) (F := F) ((s : ℂ) * z))
              * (((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))) := by
      simpa using
        (deriv_H_eq (b := b) (F := F) ((s : ℂ) * z) hwsz hF_at hF0_at)

    have hs_le1 : ‖(s : ℂ)‖ ≤ (1 : ℝ) := by
      have hsge0 : (0 : ℝ) ≤ s := le_of_lt hs.1
      have : |s| ≤ (1 : ℝ) := by
        simpa [abs_of_nonneg hsge0] using hs.2
      simpa using this

    have hmul_lt : ‖(s : ℂ) * z‖ < ε := by
      have hmul_le : ‖(s : ℂ) * z‖ ≤ ‖(s : ℂ)‖ * ‖z‖ := by
        exact norm_mul_le (s : ℂ) z
      have hsz_le : ‖(s : ℂ)‖ * ‖z‖ ≤ (1 : ℝ) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right hs_le1 (norm_nonneg z)
      have hsz_lt : ‖(s : ℂ)‖ * ‖z‖ < ε := by
        exact lt_of_le_of_lt hsz_le (by simpa [one_mul] using hznorm)
      exact lt_of_le_of_lt hmul_le hsz_lt

    have hmemV : (s : ℂ) * z ∈ V := by
      have : (s : ℂ) * z ∈ Metric.ball (0 : ℂ) ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using hmul_lt
      exact hεsub this

    have hmemU :
        (s : ℂ) * z ∈
          ({w : ℂ | ‖H (b := b) (F := F) w‖ ≤ (2 : ℝ)} ∩
           {w : ℂ | ‖r (b := b) (F := F) w‖ ≤ (1 : ℝ)}) := by
      have : (s : ℂ) * z ∈ V ∩ ({0} : Set ℂ)ᶜ := by
        refine ⟨hmemV, ?_⟩
        simpa [Set.mem_compl_singleton_iff] using hwsz
      exact hVsub this

    have hH_here : ‖H (b := b) (F := F) ((s : ℂ) * z)‖ ≤ (2 : ℝ) := hmemU.1
    have hr_here : ‖r (b := b) (F := F) ((s : ℂ) * z)‖ ≤ (1 : ℝ) := hmemU.2

    have hu :
        u s =
          (H (b := b) (F := F) ((s : ℂ) * z))
            * (((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))) * z := by
      simp [u, hder, mul_assoc]

    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z

    have hstep1 :
        ‖u s‖ ≤
          ‖H (b := b) (F := F) ((s : ℂ) * z) * (((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z)))‖
            * ‖z‖ := by
      set_option linter.unnecessarySimpa false in
      simpa [hu, mul_assoc] using
        (norm_mul_le
          (H (b := b) (F := F) ((s : ℂ) * z) * (((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))))
          z)

    have hstep2 :
        ‖H (b := b) (F := F) ((s : ℂ) * z) * (((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z)))‖
          ≤
        ‖H (b := b) (F := F) ((s : ℂ) * z)‖
          * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖ := by
      set_option linter.unnecessarySimpa false in
      simpa using
        (norm_mul_le
          (H (b := b) (F := F) ((s : ℂ) * z))
          (((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))))

    have hstep3 :
        ‖u s‖ ≤
          (‖H (b := b) (F := F) ((s : ℂ) * z)‖
            * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖) * ‖z‖ := by
      exact le_trans hstep1 (mul_le_mul_of_nonneg_right hstep2 hz0)

    have hB_le :
        ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖
          ≤
        ‖(s : ℂ) * z‖ * ‖r (b := b) (F := F) ((s : ℂ) * z)‖ := by
      set_option linter.unnecessarySimpa false in
      simpa using
        (norm_mul_le ((s : ℂ) * z) (r (b := b) (F := F) ((s : ℂ) * z)))

    have hB_le' :
        ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖
          ≤
        ‖(s : ℂ) * z‖ * (1 : ℝ) := by
      exact le_trans hB_le (mul_le_mul_of_nonneg_left hr_here (norm_nonneg ((s : ℂ) * z)))

    have hsZ_le :
        ‖(s : ℂ) * z‖ ≤ ‖(s : ℂ)‖ * ‖z‖ := by
      set_option linter.unnecessarySimpa false in
      simpa using (norm_mul_le (s : ℂ) z)

    have hsZ_le' :
        ‖(s : ℂ) * z‖ ≤ (1 : ℝ) * ‖z‖ := by
      exact le_trans hsZ_le (mul_le_mul_of_nonneg_right hs_le1 (norm_nonneg z))

    have :
        ‖u s‖ ≤ (2 : ℝ) * ‖z‖ * (1 : ℝ) * (1 : ℝ) * ‖z‖ := by
      have hA1 :
          (‖H (b := b) (F := F) ((s : ℂ) * z)‖
            * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖) * ‖z‖
            ≤
          ((2 : ℝ) * (‖(s : ℂ) * z‖ * (1 : ℝ))) * ‖z‖ := by
        have hA0 : 0 ≤ ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖ := norm_nonneg _
        have hmul1 :
            ‖H (b := b) (F := F) ((s : ℂ) * z)‖
              * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖
              ≤
            (2 : ℝ) * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖ := by
          exact mul_le_mul_of_nonneg_right hH_here hA0
        have hmul2 :
            (2 : ℝ) * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖
              ≤
            (2 : ℝ) * (‖(s : ℂ) * z‖ * (1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hB_le' (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
        have hmul3 :
            (‖H (b := b) (F := F) ((s : ℂ) * z)‖
              * ‖((s : ℂ) * z) * (r (b := b) (F := F) ((s : ℂ) * z))‖) * ‖z‖
              ≤
            ((2 : ℝ) * (‖(s : ℂ) * z‖ * (1 : ℝ))) * ‖z‖ := by
          exact mul_le_mul_of_nonneg_right (le_trans hmul1 hmul2) hz0
        simpa [mul_assoc] using hmul3

      have hA2 :
          ((2 : ℝ) * (‖(s : ℂ) * z‖ * (1 : ℝ))) * ‖z‖
            ≤
          ((2 : ℝ) * ((1 : ℝ) * ‖z‖ * (1 : ℝ))) * ‖z‖ := by
        have : ‖(s : ℂ) * z‖ * (1 : ℝ) ≤ ((1 : ℝ) * ‖z‖) * (1 : ℝ) := by
          exact mul_le_mul_of_nonneg_right hsZ_le' (by norm_num)
        have htmp0 : ((‖(↑s * z)‖ * (1 : ℝ)) * ‖z‖) ≤ ((1 : ℝ) * ‖z‖ * (1 : ℝ)) * ‖z‖ := by
          exact mul_le_mul_of_nonneg_right this hz0
        have htmp : (2 : ℝ) * ((‖(↑s * z)‖ * (1 : ℝ)) * ‖z‖) ≤ (2 : ℝ) * (((1 : ℝ) * ‖z‖ * (1 : ℝ)) * ‖z‖) := by
          exact mul_le_mul_of_nonneg_left htmp0 (by norm_num)
        simpa [mul_assoc] using htmp

      have hA3 :
          ((2 : ℝ) * ((1 : ℝ) * ‖z‖ * (1 : ℝ))) * ‖z‖
            =
          (2 : ℝ) * ‖z‖ * (1 : ℝ) * (1 : ℝ) * ‖z‖ := by
        ring_nf

      exact le_trans (le_trans hstep3 hA1) (by simpa [hA3] using hA2)

    exact this

  --------------------------------------------------------------------
  -- Glue: measurability on Ioc + bound ⇒ IntervalIntegrable on 0..1.
  --------------------------------------------------------------------

  have : IntervalIntegrable u MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
    refine intervalIntegrable_of_aestronglyMeasurable_Ioc_of_bounded
      (u := u) (M := (2 : ℝ) * ‖z‖ * (1 : ℝ) * (1 : ℝ) * ‖z‖)
      (u_mble := u_mble) (hbound := hbound)

  simpa [u] using this

end
end EulerBasel