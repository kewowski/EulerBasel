/-
EulerBasel/TopologyPunctured.lean

Small shared topology utilities for “punctured neighbourhood then patch at 0”.

Specialised to `ℂ` (snapshot-stable in this project).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic

open scoped Topology
open Filter

namespace EulerBasel

noncomputable section

/-- On the punctured neighbourhood, eventually `z ≠ 0`. -/
lemma eventually_ne_zero_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := by
  have hset : ({z : ℂ | z ≠ 0} : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
    simpa using
      (self_mem_nhdsWithin :
        ({z : ℂ | z ≠ 0} : Set ℂ) ∈ 𝓝[{z : ℂ | z ≠ 0}] (0 : ℂ))
  simpa [Filter.Eventually, Set.preimage, Set.mem_setOf_eq] using hset

/--
Upgrade `Tendsto f (𝓝[≠] 0) (𝓝 0)` to `Tendsto f (𝓝 0) (𝓝 0)`, assuming `f 0 = 0`.

This is the standard “patch at 0” move used in the EulerBasel pipeline.
-/
lemma tendsto_nhds_zero_of_tendsto_punctured {f : ℂ → ℂ}
    (hpunct : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)))
    (h0 : f 0 = 0) :
    Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε

  have hε_punct :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), dist (f z) (0 : ℂ) < ε := by
    have h := (Metric.tendsto_nhds.1 hpunct) ε hε
    simpa using h

  have himp :
      ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
        z ≠ 0 → dist (f z) (0 : ℂ) < ε := by
    exact (eventually_nhdsWithin_iff.1 hε_punct)

  filter_upwards [himp] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp [h0, hε]
  · exact hz hz0

end

end EulerBasel



