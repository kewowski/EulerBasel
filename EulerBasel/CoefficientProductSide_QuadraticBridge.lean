/-
EulerBasel/CoefficientProductSide_QuadraticBridge.lean

Bridge: quadratic expansion for `eulerLimitFun0` at `𝓝 0`.

This file derives the quadratic little-o expansion for `eulerLimitFun0` at `𝓝 0`
from the already proved product/log-derivative pipeline (Phase 2C),
using only product-side analytic tools (Euler-faithful).
-/

import EulerBasel.CoefficientDefs
import EulerBasel.CoefficientProductSide_Phase2C
import EulerBasel.TopologyPunctured
import EulerBasel.SegmentIntegralPunctured
import EulerBasel.QuadraticReconstruction

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics

namespace EulerBasel

noncomputable section

/--
Phase 2C little-o statement, rewritten as a quotient `Tendsto` on the punctured neighbourhood.
-/
lemma tendsto_logDeriv_eulerLimitFun_add_two_baselSum_div_punctured :
    Tendsto
      (fun z : ℂ => (logDeriv eulerLimitFun z + (2 * baselSum) * z) / z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (0 : ℂ)) := by
  have h :=
    logDeriv_eulerLimitFun_add_two_baselSum_mul_isLittleO_punctured
  have hgf :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        (fun z : ℂ => z) z = 0 →
          (fun z : ℂ => logDeriv eulerLimitFun z + (2 * baselSum) * z) z = 0 := by
    have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
      EulerBasel.eventually_ne_zero_punctured
    filter_upwards [hne] with z hz
    intro hz0
    exact (hz hz0).elim
  have hiff :=
    Asymptotics.isLittleO_iff_tendsto'
      (f := fun z : ℂ => logDeriv eulerLimitFun z + (2 * baselSum) * z)
      (g := fun z : ℂ => z)
      (l := 𝓝[≠] (0 : ℂ)) hgf
  -- use (→) direction: little-o ⇒ quotient tends to 0
  simpa [div_eq_mul_inv] using (hiff.1 h)

/--
Exported: quotient tends to 0 form for the quadratic bridge remainder.
This is the analytic “bridge output” that downstream files consume.
-/
lemma tendsto_eulerLimitFun0_sub_one_sub_baselSum_div :
    Tendsto
      (fun z : ℂ =>
        (eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2)) / (z ^ 2))
      (𝓝 (0 : ℂ))
      (𝓝 (0 : ℂ)) := by
  classical
  -- Define the punctured remainder term we integrate.
  let r : ℂ → ℂ := fun w => (logDeriv eulerLimitFun w + (2 * baselSum) * w) / w
  have hr : Tendsto r (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa [r] using tendsto_logDeriv_eulerLimitFun_add_two_baselSum_div_punctured

  -- Segment integral preserves punctured tendsto-to-0.
  have hseg :
      Tendsto
        (fun z : ℂ => ∫ s : ℝ in (0 : ℝ)..1, r ((s : ℂ) * z))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (0 : ℂ)) := by
    simpa [r] using tendsto_segmentIntegral_comp_mul_punctured (r := r) hr

  -- Package that segment-integral limit as the punctured quotient for the quadratic remainder.
  -- (In this project snapshot, the “ODE integration to quadratic remainder” is represented by
  -- this normalized quotient form.)
  have hquot_punct :
        Tendsto
          (fun z : ℂ =>
            (eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2)) / (z ^ 2))
          (𝓝[≠] (0 : ℂ))
          (𝓝 (0 : ℂ)) := by
        -- This is the genuine Euler-faithful reconstruction step.
        -- It does NOT follow by simp from the segment-integral lemma.
        -- Implement it via FTC on s ↦ log(F(s*z)) + baselSum*(s*z)^2 and exponentiation.
        exact tendsto_quadratic_remainder_div_from_logDeriv
          (hR := tendsto_logDeriv_eulerLimitFun_add_two_baselSum_div_punctured)

      -- Patch punctured → `𝓝 0`.
  refine EulerBasel.tendsto_nhds_zero_of_tendsto_punctured
    (f := fun z : ℂ => (eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2)) / (z ^ 2))
    ?_ ?_
  · exact hquot_punct
  · -- value at 0 is irrelevant for the limit, but we provide the required simp goal
    simp [eulerLimitFun0]

/-- Quadratic expansion for `eulerLimitFun0` at `𝓝 0` (little-o form). -/
theorem eulerLimitFun0_sub_one_sub_baselSum_isLittleO :
    (fun z : ℂ => eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2))
      =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
  -- Convert the quotient tendsto to a little-o statement using `isLittleO_iff_tendsto'`.
  have hgf :
      ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
        (fun z : ℂ => z ^ 2) z = 0 →
          (fun z : ℂ => eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2)) z = 0 := by
    refine Filter.Eventually.of_forall ?_
    intro z hz2
    have hz : z = 0 := by
      exact sq_eq_zero_iff.mp hz2
    subst hz
    simp [eulerLimitFun0]
  have hiff :=
    Asymptotics.isLittleO_iff_tendsto'
      (f := fun z : ℂ => eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2))
      (g := fun z : ℂ => z ^ 2)
      (l := 𝓝 (0 : ℂ)) hgf
  -- use (←) direction: quotient tends to 0 ⇒ little-o
  exact (hiff.2 tendsto_eulerLimitFun0_sub_one_sub_baselSum_div)

end

end EulerBasel




