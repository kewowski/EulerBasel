/-
EulerBasel/StepC_IntegrableIoc.lean

Glue lemmas for Step C:

If `u` is AE-strongly measurable on `Ioc(0,1]` (w.r.t. `volume.restrict`) and bounded there,
then `u` is `IntervalIntegrable` on `0..1`.

We keep the continuity-based lemma as a corollary.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

open scoped Topology Interval
open Filter
open MeasureTheory

namespace EulerBasel
noncomputable section

/-- Main glue lemma: measurability on `Ioc(0,1]` + boundedness ⇒ `IntervalIntegrable` on `0..1`. -/
lemma intervalIntegrable_of_aestronglyMeasurable_Ioc_of_bounded
    (u : ℝ → ℂ) (M : ℝ)
    (u_mble :
      MeasureTheory.AEStronglyMeasurable u
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖u s‖ ≤ M) :
    IntervalIntegrable u MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  have h01 : (0 : ℝ) ≤ 1 := by exact zero_le_one
  -- Reduce IntervalIntegrable to IntegrableOn over Ioc.
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := MeasureTheory.volume) h01).2 ?_
  -- Goal: IntegrableOn u (Ioc 0 1) volume, i.e. Integrable u (volume.restrict (Ioc 0 1)).
  -- Work with μI := volume.restrict (Ioc 0 1).
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)

  set_option linter.unnecessarySimpa false in
  have hs_finite : μI Set.univ ≠ ⊤ := by
    -- μI univ = volume (Ioc 0 1)
    have : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ :=
      (measure_Ioc_lt_top : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) < ⊤).ne
    simpa [μI, Measure.restrict_apply, Set.inter_univ, measurableSet_Ioc] using this
  have u_bdd : ∀ᵐ s ∂μI, ‖u s‖ ≤ M := by
    -- This is exactly an AE statement on the restricted measure.
    -- Use `ae_restrict_iff'` to reduce to a pointwise bound on Ioc.
    refine (MeasureTheory.ae_restrict_iff'
      (μ := MeasureTheory.volume)
      (s := Set.Ioc (0 : ℝ) 1)
      (p := fun s : ℝ => ‖u s‖ ≤ M)
      (by 
        exact (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1)))).2 ?_
    refine MeasureTheory.ae_of_all (μ := MeasureTheory.volume) ?_
    intro s hs
    exact hbound s hs

  have hu_univ : IntegrableOn u (Set.univ : Set ℝ) μI := by
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (μ := μI) (s := (Set.univ : Set ℝ))
      (s_finite := hs_finite)
      (f_mble := by simpa [μI] using u_mble)
      (M := M)
      (f_bdd := by
        simpa [μI, Measure.restrict_univ] using u_bdd)

  -- Convert back: IntegrableOn u (Ioc 0 1) volume.
  -- `IntegrableOn u (Ioc 0 1) volume` is definitionaly `Integrable u μI`.
  simpa [IntegrableOn, μI, Measure.restrict_univ] using hu_univ

/-- Corollary: continuity on `Ioc(0,1]` + boundedness ⇒ `IntervalIntegrable` on `0..1`. -/
lemma intervalIntegrable_of_continuousOn_Ioc_of_bounded
    (u : ℝ → ℂ) (M : ℝ)
    (hcont : ContinuousOn u (Set.Ioc (0 : ℝ) 1))
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖u s‖ ≤ M) :
    IntervalIntegrable u MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  refine intervalIntegrable_of_aestronglyMeasurable_Ioc_of_bounded
    (u := u) (M := M)
    (u_mble := ?_) (hbound := hbound)
  exact hcont.aestronglyMeasurable (by
    exact (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1)))

end
end EulerBasel
