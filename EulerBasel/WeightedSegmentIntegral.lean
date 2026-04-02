import EulerBasel.TopologyPunctured
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics
open scoped Interval

namespace EulerBasel

/-!
Weighted segment integral along s ↦ (s:ℂ)*z.

Goal: if r(z) → 0 on 𝓝[≠] 0, then
  z ↦ ∫ s in 0..1, (s:ℂ) * r((s:ℂ)*z)  → 0 on 𝓝[≠] 0.
-/

noncomputable section

lemma tendsto_segmentIntegral_comp_mul_punctured_weighted (r : ℂ → ℂ)
    (hr : Tendsto r (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ))) :
    Tendsto (fun z : ℂ => ∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) * r ((s : ℂ) * z))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (0 : ℂ)) := by
  classical
  -- same structure as the unweighted lemma
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by nlinarith [hε]

  let A : Set ℂ := {w : ℂ | ‖r w‖ < ε / 2}

  have hA_mem : A ∈ 𝓝[≠] (0 : ℂ) := by
    have hball : Metric.ball (0 : ℂ) (ε / 2) ∈ 𝓝 (0 : ℂ) := by
      simpa using (Metric.ball_mem_nhds (0 : ℂ) hε2)
    have hEv : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), r w ∈ Metric.ball (0 : ℂ) (ε / 2) :=
      hr.eventually hball
    have : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), ‖r w‖ < ε / 2 := by
      refine hEv.mono ?_
      intro w hw
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    simpa [A, Filter.eventually_iff, Set.setOf_mem_eq] using this

  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hA_mem with ⟨t, ht0, ht⟩
  rcases Metric.mem_nhds_iff.1 ht0 with ⟨ρ, hρpos, hρsub⟩
  have hpunct_ball_sub :
      (Metric.ball (0 : ℂ) ρ ∩ ({w : ℂ | w ≠ 0} : Set ℂ)) ⊆ A := by
    intro w hw
    have : w ∈ t ∩ ({w : ℂ | w ≠ 0} : Set ℂ) := by
      refine ⟨?_, hw.2⟩
      exact hρsub hw.1
    exact ht this

  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
    EulerBasel.eventually_ne_zero_punctured

  -- as in your unweighted lemma: work with ‖z‖ < ρ
  have hzball : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ < ρ := by
    have hzball0 : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ‖z‖ < ρ := by
      have hb : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := by
        exact Metric.ball_mem_nhds (0 : ℂ) (by exact_mod_cast hρpos)
      have hset : ({z : ℂ | ‖z‖ < ρ} : Set ℂ) = Metric.ball (0 : ℂ) ρ := by
        ext z
        simp [Metric.mem_ball, dist_eq_norm]
      have : {z : ℂ | ‖z‖ < ρ} ∈ 𝓝 (0 : ℂ) := by
        simpa [hset] using hb
      simpa [Filter.eventually_iff] using this
    exact hzball0.filter_mono nhdsWithin_le_nhds

  have hmain :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        ‖(∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) * r ((s : ℂ) * z))‖ < ε := by
    filter_upwards [hne, hzball] with z hzne hzρ

    have hbound :
        ∀ s : ℝ, s ∈ (Ι (0 : ℝ) (1 : ℝ)) →
          ‖(s : ℂ) * r ((s : ℂ) * z)‖ ≤ (ε / 2 : ℝ) := by
      intro s hsI
      have hsI' : s ∈ Set.Ioc (0 : ℝ) (1 : ℝ) := by
        simpa [Set.uIoc] using hsI
      have hspos : 0 < s := hsI'.1
      have hsle1 : s ≤ 1 := hsI'.2

      have hsneC : (s : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hspos)
      have hsne : (s : ℂ) * z ≠ 0 := mul_ne_zero hsneC hzne

      have habs : |s| ≤ (1 : ℝ) := by
        have hsnonneg : 0 ≤ s := le_of_lt hspos
        simpa [abs_of_nonneg hsnonneg] using hsle1

      have hsNorm : ‖(s : ℂ)‖ ≤ (1 : ℝ) := by
        simpa using habs

      have hnorm_mul : ‖(s : ℂ) * z‖ ≤ ‖z‖ := by
        simpa [norm_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hsNorm (norm_nonneg z)

      have hszlt : ‖(s : ℂ) * z‖ < ρ := lt_of_le_of_lt hnorm_mul hzρ
      have hsball : (s : ℂ) * z ∈ Metric.ball (0 : ℂ) ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hszlt

      have hsA : (s : ℂ) * z ∈ A :=
        hpunct_ball_sub ⟨hsball, by simpa [Set.mem_setOf_eq] using hsne⟩

      have hrlt : ‖r ((s : ℂ) * z)‖ < ε / 2 := by
        simpa [A, Set.mem_setOf_eq] using hsA

      -- now bound the product by using ‖s‖ ≤ 1
      have : ‖(s : ℂ) * r ((s : ℂ) * z)‖ ≤ ‖r ((s : ℂ) * z)‖ := by
        simpa [norm_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hsNorm (norm_nonneg (r ((s : ℂ) * z)))

      exact le_trans this (le_of_lt hrlt)

    have hle' :
        ‖(∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) * r ((s : ℂ) * z))‖
          ≤ (ε / 2 : ℝ) * |(1 : ℝ) - (0 : ℝ)| := by
      simpa using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := (1 : ℝ)) (C := (ε / 2 : ℝ))
          (f := fun s : ℝ => (s : ℂ) * r ((s : ℂ) * z)) hbound)

    have hle : ‖(∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) * r ((s : ℂ) * z))‖ ≤ (ε / 2 : ℝ) := by
      simpa using (le_trans hle' (by simp))

    have : (ε / 2 : ℝ) < ε := by nlinarith [hε]
    exact lt_of_le_of_lt hle this

  have :
      ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ),
        dist (∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) * r ((s : ℂ) * x)) (0 : ℂ) < ε := by
    refine hmain.mono ?_
    intro x hx
    simpa [dist_eq_norm] using hx

  exact this

end

end EulerBasel
