import EulerBasel.LogFTC
import EulerBasel.NearZeroSegment

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Topology Interval
open Filter
open MeasureTheory

namespace EulerBasel
noncomputable section

/-
Glue: convert the Step C “core” identity

  ∫ s in 0..1, deriv(H b F) ((s:ℂ)*z) * z = H b F z - 1

into the weighted form needed for Step D:

  H b F z - 1 = z^2 * ∫ s in 0..1, (s:ℂ) * (H b F ((s:ℂ)*z) * r b F ((s:ℂ)*z)).
-/

private lemma integrand_rewrite
    (b : ℂ) (F : ℂ → ℂ) (z : ℂ) (s : ℝ)
    (hz : z ∈ nearZeroPunctured)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hFdiff : ∀ {w : ℂ}, w ∈ nearZeroPunctured → DifferentiableAt ℂ F w)
    (hFne   : ∀ {w : ℂ}, w ∈ nearZeroPunctured → F w ≠ 0) :
    (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z
      =
    (z ^ 2) * ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
          * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
  have hseg : ((s : ℂ) * z) ∈ nearZeroPunctured :=
    segMul_mem_nearZeroPunctured (z := z) hz hs
  have hwsz : (s : ℂ) * z ≠ 0 :=
    (mem_nearZeroPunctured_iff (z := (s : ℂ) * z)).1 hseg |>.2
  have hF_at : DifferentiableAt ℂ F ((s : ℂ) * z) := hFdiff (w := (s : ℂ) * z) hseg
  have hF0_at : F ((s : ℂ) * z) ≠ 0 := hFne (w := (s : ℂ) * z) hseg

  have hder :
      deriv (H (b := b) (F := F)) ((s : ℂ) * z)
        = (H (b := b) (F := F) ((s : ℂ) * z))
            * (((s : ℂ) * z) * EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)) := by
    simpa using (deriv_H_eq (b := b) (F := F) ((s : ℂ) * z) hwsz hF_at hF0_at)

  calc
    (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z
        = ((H (b := b) (F := F) ((s : ℂ) * z))
            * (((s : ℂ) * z) * EulerBasel.r (b := b) (F := F) ((s : ℂ) * z))) * z := by
              simp [hder]
    _   = (z ^ 2) * ((s : ℂ) *
          ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
              ring_nf

theorem eventually_coreWeighted_of_stepC_core
    (b : ℂ) (F : ℂ → ℂ)
    (hnear : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured)
    (hFdiff : ∀ {w : ℂ}, w ∈ nearZeroPunctured → DifferentiableAt ℂ F w)
    (hFne   : ∀ {w : ℂ}, w ∈ nearZeroPunctured → F w ≠ 0)
    (hcore :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        ∫ s : ℝ in (0 : ℝ)..1,
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z
          =
        (H (b := b) (F := F) z) - (1 : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      (H (b := b) (F := F) z) - (1 : ℂ) =
        (z ^ 2) * ∫ s : ℝ in (0 : ℝ)..1,
          (s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z))) := by
  filter_upwards [hnear, hcore] with z hz hzcore

  have hae01 :
      ∀ᵐ s : ℝ ∂(volume),
        s ∈ Set.Ioc (0 : ℝ) 1 →
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z
            =
          (z ^ 2) * ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
    refine MeasureTheory.ae_of_all (μ := volume) ?_
    intro s hs
    exact integrand_rewrite (b := b) (F := F) (z := z) (s := s)
      (hz := hz) (hs := hs) (hFdiff := hFdiff) (hFne := hFne)

  have hae10 :
      ∀ᵐ s : ℝ ∂(volume),
        s ∈ Set.Ioc (1 : ℝ) 0 →
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z
            =
          (z ^ 2) * ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
    refine MeasureTheory.ae_of_all (μ := volume) ?_
    intro s hs
    rcases hs with ⟨hs1, hs2⟩
    exfalso
    exact (not_lt_of_ge (show (0 : ℝ) ≤ (1 : ℝ) from zero_le_one) (lt_of_lt_of_le hs1 hs2))

  have hcongr :
      (∫ s : ℝ in (0 : ℝ)..1,
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
        =
      (∫ s : ℝ in (0 : ℝ)..1,
          (z ^ 2) * ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z))))) := by
    simpa using
      (intervalIntegral.integral_congr_ae'
        (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
        (f := fun s : ℝ => (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
        (g := fun s : ℝ =>
          (z ^ 2) * ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))))
        hae01 hae10)

  have hrew_int :
      (∫ s : ℝ in (0 : ℝ)..1,
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
        =
      (z ^ 2) * ∫ s : ℝ in (0 : ℝ)..1,
        ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
          * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
    calc
      (∫ s : ℝ in (0 : ℝ)..1,
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
          =
        (∫ s : ℝ in (0 : ℝ)..1,
          (z ^ 2) * ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z))))) := hcongr
      _ =
        (z ^ 2) * ∫ s : ℝ in (0 : ℝ)..1,
          ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
            * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
          exact
            (intervalIntegral.integral_const_mul (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
              (r := (z ^ 2))
              (f := fun s : ℝ =>
                ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
                  * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z))))))

  calc
    (H (b := b) (F := F) z) - (1 : ℂ)
        =
      (∫ s : ℝ in (0 : ℝ)..1,
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z) := by
      simpa using hzcore.symm
    _ =
      (z ^ 2) * ∫ s : ℝ in (0 : ℝ)..1,
        ((s : ℂ) * ((H (b := b) (F := F) ((s : ℂ) * z))
          * (EulerBasel.r (b := b) (F := F) ((s : ℂ) * z)))) := by
      simpa [mul_assoc] using hrew_int

end
end EulerBasel

