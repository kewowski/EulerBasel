/-
EulerBasel/CoefficientProductSide.lean

Product-side coefficient extraction interface.

Exported goal:
  sinDivPiZ0 z = 1 - baselSum * z^2 + o(z^2)  as z → 0

We work with the 0-patched Euler limit function `eulerLimitFun0` (value 1 at z = 0),
transfer the quadratic expansion to `sinDivPiZ0` using punctured equality, and
the quotient/tendsto characterization of little-o.
-/

import EulerBasel.CoefficientDefs
import EulerBasel.EulerSumLimit
import EulerBasel.CoefficientEulerSumLimit
import EulerBasel.CoefficientEulerRationalTsum
import EulerBasel.EulerLimitFunEqSine
import EulerBasel.TopologyPunctured
import EulerBasel.CoefficientProductSide_Phase2C
import EulerBasel.CoefficientProductSide_QuadraticBridge

import Mathlib.Analysis.Asymptotics.Lemmas

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics

namespace EulerBasel

noncomputable section

/-- Eventually near `0`, we lie in the ball `Metric.ball 0 (1/2)`. -/
lemma eventually_mem_ball_half :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) := by
  exact Metric.ball_mem_nhds (0 : ℂ) (by norm_num)

/-- Eventually on the punctured neighbourhood, `z ∈ nearZeroPunctured`. -/
lemma eventually_mem_nearZeroPunctured_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured := by
  classical
  have hball :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) := by
    exact (eventually_mem_ball_half).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := EulerBasel.eventually_ne_zero_punctured
  filter_upwards [hball, hne] with z hzBall hz0
  -- `nearZeroPunctured = ball(0,1/2) \ {0}` in this project.
  simpa [nearZeroPunctured, hz0] using And.intro hzBall hz0

/-- Eventually on the punctured neighbourhood, `eulerLimitFun z = sinDivPiZ0 z`. -/
lemma eventually_eulerLimitFun_eq_sinDivPiZ0_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), eulerLimitFun z = sinDivPiZ0 z := by
  have hmem : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured :=
    eventually_mem_nearZeroPunctured_punctured
  filter_upwards [hmem] with z hz
  exact eulerLimitFun_eq_sinDivPiZ0_of_mem_nearZeroPunctured (z := z) (hz := hz)

/-- On the punctured neighbourhood, `eulerLimitFun0 = eulerLimitFun`. -/
lemma eventually_eulerLimitFun0_eq_eulerLimitFun_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), eulerLimitFun0 z = eulerLimitFun z := by
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
    EulerBasel.eventually_ne_zero_punctured
  filter_upwards [hne] with z hz
  simp [eulerLimitFun0, hz]

/-- Eventually on the punctured neighbourhood, `eulerLimitFun0 z = sinDivPiZ0 z`. -/
lemma eventually_eulerLimitFun0_eq_sinDivPiZ0_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), eulerLimitFun0 z = sinDivPiZ0 z := by
  have h₁ : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), eulerLimitFun0 z = eulerLimitFun z :=
    eventually_eulerLimitFun0_eq_eulerLimitFun_punctured
  have h₂ : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), eulerLimitFun z = sinDivPiZ0 z :=
    eventually_eulerLimitFun_eq_sinDivPiZ0_punctured
  filter_upwards [h₁, h₂] with z hz1 hz2
  exact hz1.trans hz2

/--
Transfer lemma:

If `eulerLimitFun0` has the quadratic little-o expansion at `𝓝 0`,
then `sinDivPiZ0` has the same expansion at `𝓝 0`.

The transfer uses punctured equality and the quotient/tendsto characterization of little-o.
-/
theorem sinDivPiZ0_sub_one_sub_baselSum_isLittleO_of_eulerLimitFun0
    (hE :
      (fun z : ℂ => eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2))
        =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2)) :
    (fun z : ℂ => sinDivPiZ0 z - ((1 : ℂ) - baselSum * z ^ 2))
      =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
  let fE : ℂ → ℂ := fun z => eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2)
  let fS : ℂ → ℂ := fun z => sinDivPiZ0 z - ((1 : ℂ) - baselSum * z ^ 2)
  let g : ℂ → ℂ := fun z => z ^ 2

  have hzeroS : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), g z = 0 → fS z = 0 := by
    refine Filter.Eventually.of_forall ?_
    intro z hz
    have hz0 : z = 0 := by
      by_contra hz0
      exact (pow_ne_zero 2 hz0) hz
    subst hz0
    simp [fS, sinDivPiZ0]

  have hE_tendsto : Tendsto (fun z : ℂ => fE z / g z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa [fE, g] using (hE.tendsto_div_nhds_zero)

  have hE_tendsto_punct :
      Tendsto (fun z : ℂ => fE z / g z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    hE_tendsto.comp nhdsWithin_le_nhds

  have hquot_eq_punct :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), fS z / g z = fE z / g z := by
    have heq : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), eulerLimitFun0 z = sinDivPiZ0 z :=
      eventually_eulerLimitFun0_eq_sinDivPiZ0_punctured
    filter_upwards [heq] with z hz
    simp [fE, fS, hz]

  have hquot_eq_punct' :
      (fun z : ℂ => fE z / g z) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z : ℂ => fS z / g z) := by
    refine hquot_eq_punct.mono ?_
    intro z hz
    exact hz.symm

  have hS_tendsto_punct :
      Tendsto (fun z : ℂ => fS z / g z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have := (tendsto_congr' hquot_eq_punct').1 hE_tendsto_punct
    simpa using this

  have hS_tendsto :
      Tendsto (fun z : ℂ => fS z / g z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    refine EulerBasel.tendsto_nhds_zero_of_tendsto_punctured (f := fun z => fS z / g z) ?_ ?_
    · exact hS_tendsto_punct
    · simp [fS, g, sinDivPiZ0]

  have hiff :=
    Asymptotics.isLittleO_iff_tendsto' (f := fS) (g := g) (l := 𝓝 (0 : ℂ)) hzeroS
  exact hiff.2 hS_tendsto

/-- Main product-side lemma exported to the rest of the pipeline. -/
theorem sinDivPiZ0_sub_one_sub_baselSum_isLittleO :
    (fun z : ℂ => sinDivPiZ0 z - ((1 : ℂ) - baselSum * z ^ 2))
      =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
  exact sinDivPiZ0_sub_one_sub_baselSum_isLittleO_of_eulerLimitFun0
    eulerLimitFun0_sub_one_sub_baselSum_isLittleO

end

end EulerBasel

