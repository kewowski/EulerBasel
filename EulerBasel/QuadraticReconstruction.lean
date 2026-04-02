/-
EulerBasel/QuadraticReconstruction.lean

Euler-faithful reconstruction step:

From Phase2C control of the logarithmic derivative on the punctured neighbourhood,
derive the quadratic expansion of the 0-patched limit function at 0.

This file intentionally avoids sine-side asymptotics.
-/

import EulerBasel.TopologyPunctured
import EulerBasel.SegmentIntegralPunctured
import EulerBasel.WeightedSegmentIntegral
import EulerBasel.CoefficientEulerLicensing
import EulerBasel.EulerLimitFunDeriv
import EulerBasel.LogFTC
import EulerBasel.NearZeroSegment
import EulerBasel.QuadraticReconstruction_FTC
import EulerBasel.StepC_CoreWeighted
import EulerBasel.QuadraticReconstruction_StepD
import EulerBasel.DerivHMulZ
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics
open scoped Interval

namespace EulerBasel

noncomputable section
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false


/-- 0-patched Euler limit function: value at 0 is 1. -/
def eulerLimitFun0 (z : ℂ) : ℂ :=
  if z = 0 then (1 : ℂ) else eulerLimitFun z

/-
Local helper (kept private): `Tendsto eulerLimitFun0 (𝓝 0) (𝓝 1)`.

Note: there is no existing project lemma for this elsewhere (confirmed by `rg`).
We keep this lemma as the dedicated place to finish the Euler-faithful “sin z / z → 1”
argument later (likely via `Complex.isEquivalent_sin` and `IsEquivalent.div`).
-/
private lemma tendsto_eulerLimitFun0_nhds_zero :
    
    Tendsto eulerLimitFun0 (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  -- We prove the quotient limit on the punctured filter using `IsLittleO`,
  -- then patch at 0 using `eulerLimitFun0 0 = 1`.
  have hsin_o :
      (fun w : ℂ => Complex.sin w - w) =o[𝓝 (0 : ℂ)] (fun w : ℂ => w) := by
    simpa [Pi.sub_apply] using (Complex.isEquivalent_sin)
  -- Set p = π as a complex number.
  let p : ℂ := ((Real.pi : ℝ) : ℂ)
  have hp0 : p ≠ 0 := by
    -- p = ((Real.pi : ℝ) : ℂ)
    simpa [p] using (show ((Real.pi : ℝ) : ℂ) ≠ 0 by
      exact_mod_cast (Real.pi_ne_zero : (Real.pi : ℝ) ≠ 0))

  -- Define scaled numerator/denominator.
  let num : ℂ → ℂ := fun z => Complex.sin (p * z) - (p * z)
  let den : ℂ → ℂ := fun z => p * z

  -- Show `num = o(den)` at 0 by composing the little-o statement with `z ↦ p*z`.
  have hscaled : num =o[𝓝 (0 : ℂ)] den := by
    have ht : Tendsto (fun z : ℂ => p * z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using ((continuous_const.mul continuous_id).tendsto (0 : ℂ))
    simpa [num, den, Function.comp, Pi.sub_apply] using (hsin_o.comp_tendsto ht)

  -- Divide: (num/den) → 0 at 0, hence also on the punctured neighbourhood.
  have hdiv0 :
      Tendsto (fun z : ℂ => num z / den z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa using hscaled.tendsto_div_nhds_zero

  have hdiv :
      Tendsto (fun z : ℂ => num z / den z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    hdiv0.mono_left nhdsWithin_le_nhds

  -- On `z ≠ 0`, `sin(p*z)/(p*z) = 1 + num/den`.
  have hrew :
      (fun z : ℂ => eulerLimitFun z)
        =ᶠ[𝓝[≠] (0 : ℂ)]
          (fun z : ℂ => (1 : ℂ) + num z / den z) := by
    have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
      eventually_ne_zero_punctured
    filter_upwards [hne] with z hz
    have hden : den z ≠ 0 := mul_ne_zero hp0 hz
    have hsum : Complex.sin (p * z) = den z + num z := by
      simp [num, den, sub_eq_add_neg]
    have hfrac :
        Complex.sin (p * z) / den z = (1 : ℂ) + num z / den z := by
      calc
        Complex.sin (p * z) / den z
            = (den z + num z) / den z := by simpa [hsum]
        _   = den z / den z + num z / den z := by
              simp [add_div]
        _   = (1 : ℂ) + num z / den z := by
              simp [hden]
    simpa [eulerLimitFun, den] using hfrac

  -- Therefore `eulerLimitFun → 1` on the punctured neighbourhood.
  have ht_euler_punct :
      Tendsto eulerLimitFun (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have : Tendsto (fun z : ℂ => (1 : ℂ) + num z / den z)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((1 : ℂ) + (0 : ℂ))) :=
      tendsto_const_nhds.add hdiv
    have := this.congr' hrew.symm
    simpa using this

  -- Patch at 0: use the punctured neighbourhood fact, plus `eulerLimitFun0 0 = 1`.
  refine (tendsto_def.2 ?_)
  intro V hV
  rcases mem_nhds_iff.1 hV with ⟨W, hWV, hWopen, h1W⟩
  have h1V : (1 : ℂ) ∈ V := hWV h1W

  have hpre :
      {z : ℂ | eulerLimitFun z ∈ V} ∈ 𝓝[≠] (0 : ℂ) :=
    ht_euler_punct.eventually hV

  rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre) with ⟨t, ht0, htsub⟩

  refine Filter.mem_of_superset ht0 ?_
  intro z hz
  by_cases hz0 : z = 0
  · simpa [eulerLimitFun0, hz0, h1V]
  · have hz' : z ∈ t ∩ ({0} : Set ℂ)ᶜ := by
      refine ⟨hz, ?_⟩
      simpa [Set.mem_compl_singleton_iff] using hz0
    have : eulerLimitFun z ∈ V := htsub hz'
    simpa [eulerLimitFun0, hz0] using this

/-- Small helper: `(s:ℂ) * z → z` as `s → 1` in `ℝ`. -/
private lemma tendsto_ofReal_mul_const_nhds_one (z : ℂ) :
    Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝 (1 : ℝ)) (𝓝 z) := by
  have hcont : Continuous (fun s : ℝ => (s : ℂ) * z) :=
    (Complex.continuous_ofReal.mul continuous_const)
  have ht :
      Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℂ) * z)) :=
    hcont.tendsto (1 : ℝ)
  simpa [one_mul] using ht

/-
Main reconstruction lemma (to be used by CoefficientProductSide_QuadraticBridge.lean).

Input:
  r(z) := (logDeriv F z + (2*b)*z) / z  → 0 on 𝓝[≠] 0

Output:
  (F0(z) - (1 - b*z^2)) / z^2  → 0 on 𝓝[≠] 0
-/
lemma tendsto_quadratic_remainder_div_from_logDeriv
    (hR :
      Tendsto
        (fun z : ℂ => (logDeriv eulerLimitFun z + (2 * baselSum) * z) / z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun z : ℂ =>
        (eulerLimitFun0 z - ((1 : ℂ) - baselSum * z ^ 2)) / (z ^ 2))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (0 : ℂ)) := by
  classical

  -- Shorthand: b = baselSum, F = eulerLimitFun.
  set b : ℂ := baselSum with hb
  set F : ℂ → ℂ := eulerLimitFun with hF

  -- The “small term” r(z) = (logDeriv F z + 2*b*z)/z.
  let r : ℂ → ℂ := fun z => (logDeriv F z + (2 * b) * z) / z
  have hr : Tendsto r (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa [r, b, F, hb, hF, mul_assoc, mul_left_comm, mul_comm] using hR

  -- Use the project integrating factor `ScratchLogFTC.H`.
  let Hfun : ℂ → ℂ := H (b := b) (F := F)
  let H0 : ℂ → ℂ := fun w => eulerLimitFun0 w * NormedSpace.exp (b * w ^ 2)

  have hH0_def : ∀ z : ℂ, H0 z = eulerLimitFun0 z * NormedSpace.exp (b * z ^ 2) := by
    intro z; rfl

  -- On w ≠ 0, H0 = Hfun.
  have hH0_eq_Hfun : ∀ {w : ℂ}, w ≠ 0 → H0 w = Hfun w := by
    intro w hw
    simp [H0, Hfun, eulerLimitFun0, hw, hF, H]

  -- H0(0) = 1.
  have hH0_zero : H0 0 = (1 : ℂ) := by
    simp [H0, eulerLimitFun0]

  -- Non-vanishing of F on nearZeroPunctured.
  have hFne : ∀ {w : ℂ}, w ∈ nearZeroPunctured → F w ≠ 0 := by
    intro w hw
    simpa [hF] using
      (eulerLimitFun_ne_zero_of_mem_nearZeroPunctured (z := w) hw)

  -- Differentiability of F on nearZeroPunctured (project API).
  have hFdiff : ∀ {w : ℂ}, w ∈ nearZeroPunctured → DifferentiableAt ℂ F w := by
    intro w hw
    simpa [hF] using
      (differentiableAt_eulerLimitFun_of_mem_nearZeroPunctured (z := w) hw)

  --------------------------------------------------------------------
  -- Step A: eventually, z lies in nearZeroPunctured.
  --------------------------------------------------------------------
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ nearZeroPunctured := by
    have hnorm :
        ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ‖z‖ < ((1 / 2 : ℝ)) := by
      have hmem : Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
      refine Filter.mem_of_superset hmem ?_
      intro z hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hnorm_punct :
        ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ < ((1 / 2 : ℝ)) := by
      refine (eventually_nhdsWithin_iff.2 ?_)
      filter_upwards [hnorm] with z hz _
      exact hz
    have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
      eventually_ne_zero_punctured
    filter_upwards [hnorm_punct, hne] with z hznorm hz0
    exact (mem_nearZeroPunctured_iff (z := z)).2 ⟨hznorm, hz0⟩

  --------------------------------------------------------------------
  -- Step B: g(w) := Hfun(w) * r(w), show g → 0, then the weighted segment integral → 0.
  --------------------------------------------------------------------
  let g : ℂ → ℂ := fun w => Hfun w * r w

  -- We will need a clean tendsto for H0 at 0 later; keep it isolated.
  have hH0_nhds : Tendsto H0 (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hE : Tendsto eulerLimitFun0 (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) :=
      tendsto_eulerLimitFun0_nhds_zero

    have hExp :
        Tendsto (fun w : ℂ => NormedSpace.exp (b * w ^ 2))
          (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      have hinner : ContinuousAt (fun w : ℂ => b * w ^ 2) (0 : ℂ) := by
        simpa using (continuous_const.mul (continuous_id.pow 2)).continuousAt
      have hexp0 : ContinuousAt NormedSpace.exp (b * (0 : ℂ) ^ 2) := by
        exact (hasDerivAt_exp (x := (b * (0 : ℂ) ^ 2))).continuousAt
      have hexp : ContinuousAt (fun w : ℂ => NormedSpace.exp (b * w ^ 2)) (0 : ℂ) := by
        simpa using (hexp0.comp (x := (0 : ℂ)) hinner)
      simpa using hexp.tendsto

    have :
        Tendsto (fun w : ℂ => eulerLimitFun0 w * NormedSpace.exp (b * w ^ 2))
          (𝓝 (0 : ℂ)) (𝓝 ((1 : ℂ) * (1 : ℂ))) :=
      hE.mul hExp
    simpa [H0, one_mul] using this

  have hH0_punct : Tendsto H0 (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) :=
    hH0_nhds.mono_left nhdsWithin_le_nhds

  -- Replace H0 by Hfun on the punctured neighbourhood.
  have hHfun_punct : Tendsto Hfun (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    refine (hH0_punct.congr' ?_)
    have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 :=
      eventually_ne_zero_punctured
    filter_upwards [hne] with z hz
    exact (hH0_eq_Hfun (w := z) hz)

  have hg : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have :
        Tendsto (fun w : ℂ => Hfun w * r w) (𝓝[≠] (0 : ℂ))
          (𝓝 ((1 : ℂ) * (0 : ℂ))) :=
      hHfun_punct.mul hr
    simpa [g] using (this.trans (by simpa))

  have hI :
      Tendsto
        (fun z : ℂ => ∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) * g ((s : ℂ) * z))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (0 : ℂ)) := by
    simpa [g] using
      tendsto_segmentIntegral_comp_mul_punctured_weighted g hg

  --------------------------------------------------------------------
  -- Step C integrability hypothesis (packaged elsewhere).
  --------------------------------------------------------------------
  have hhint :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        IntervalIntegrable
          (fun s : ℝ => (deriv Hfun ((s : ℂ) * z)) * z)
          MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
    simpa [Hfun] using
      (EulerBasel.eventually_hint_derivH_mul_z
        (b := b) (F := F)
        (hnear := hnear)
        (hFdiff := hFdiff)
        (hFne := hFne)
        (hHfun := hHfun_punct)
        (hr := hr))

  --------------------------------------------------------------------
  -- Step C: Apply the FTC identity to H along the segment, with fa = 1.
  --------------------------------------------------------------------
  have hcore :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        (∫ s : ℝ in (0 : ℝ)..1,
            (deriv Hfun ((s : ℂ) * z)) * z)
          =
          (Hfun z) - (1 : ℂ) := by
    filter_upwards [hnear, hhint] with z hz hint

    have hz_ne : z ≠ 0 := (mem_nearZeroPunctured_iff (z := z)).1 hz |>.2

    have h0 :
        Tendsto (fun s : ℝ => Hfun ((s : ℂ) * z))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      -- (s:ℂ)*z → 0 as s → 0+
      have hcoe0 :
          Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        have h : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
          simpa using (Complex.continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ)))
        exact h.mono_left nhdsWithin_le_nhds
      have hsz0 :
          Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        simpa using (hcoe0.mul_const z)

      have hH0seg :
          Tendsto (fun s : ℝ => H0 ((s : ℂ) * z)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) :=
        hH0_nhds.comp hsz0

      -- Replace H0 by Hfun for s ≠ 0.
      refine (hH0seg.congr' ?_)
      have hsIoi : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ∈ Set.Ioi (0 : ℝ) := by
        -- `Ioi 0` is the defining set for `𝓝[>] 0`
        simpa [nhdsWithin] using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
      have hsne : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ≠ 0 :=
        hsIoi.mono (fun s hs => ne_of_gt hs)

      filter_upwards [hsne] with s hsne
      have hsneC : (s : ℂ) ≠ 0 := by
        exact_mod_cast hsne
      have hwsz : (s : ℂ) * z ≠ 0 := mul_ne_zero hsneC hz_ne
      simpa [H0, Hfun] using (hH0_eq_Hfun (w := (s : ℂ) * z) hwsz)

    have h1 :
        Tendsto (fun s : ℝ => Hfun ((s : ℂ) * z))
          (𝓝[<] (1 : ℝ)) (𝓝 (Hfun z)) := by
      -- (s:ℂ)*z → z as s → 1-
      have hmul :
          Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
        have ht : Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝 (1 : ℝ)) (𝓝 z) :=
          tendsto_ofReal_mul_const_nhds_one z
        exact ht.mono_left nhdsWithin_le_nhds

      -- Continuity of Hfun at z (from differentiability of F at z, plus exp continuity).
      have hcontH : ContinuousAt Hfun z := by
        have hFcont : ContinuousAt F z := (hFdiff (w := z) hz).continuousAt

        have hinner : ContinuousAt (fun w : ℂ => b * w ^ 2) z := by
          simpa using (continuous_const.mul (continuous_id.pow 2)).continuousAt

        have hexp0 : ContinuousAt NormedSpace.exp (b * z ^ 2) := by
          exact (hasDerivAt_exp (x := (b * z ^ 2))).continuousAt

        have hexp : ContinuousAt (fun w : ℂ => NormedSpace.exp (b * w ^ 2)) z := by
          simpa [Function.comp] using (hexp0.comp (x := z) hinner)

        simpa [Hfun, H] using hFcont.mul hexp

      exact (hcontH.tendsto.comp hmul)
    
    simpa [Hfun] using
      (EulerBasel.segmentFTC_H_eq
        (b := b) (F := F) (z := z) (hz := hz)
        (hFdiff := fun {w} hw => hFdiff (w := w) hw)
        (hint := hint) (fa := (1 : ℂ)) (h0 := h0) (h1 := h1))

  --------------------------------------------------------------------
  -- Step C -> weighted form (use the already-proved scratch helper).
  --------------------------------------------------------------------
  have hcoreWeighted :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        Hfun z - (1 : ℂ) =
          (z ^ 2) * ∫ s : ℝ in 0..1, (s : ℂ) * g ((s : ℂ) * z) := by
    -- Our hcore is over (0..1); the helper expects 0..1 on the RHS with g = H*r.
    -- We package it by providing hcore to the helper; it handles the integrand algebra.
    have hcore0 :
        ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
          (∫ s : ℝ in 0..1, (deriv Hfun ((s : ℂ) * z)) * z) = (Hfun z) - (1 : ℂ) := by
      -- intervalIntegral endpoints have measure zero; use the same core identity.
      -- The existing `segmentFTC_H_eq` statement is already `0..1`, and your `hcore`
      -- is `0..1` in the intended final form. If you later normalize `hcore` to `0..1`,
      -- this `simpa` will become trivial.
      --
      -- For now, we just reuse `hcore` directly by rewriting bounds in the file later if needed.
      simpa using hcore

    -- Now use the exported helper:
    --   hcore0 : ∫ 0..1 deriv(H)*z = H z - 1
    -- gives:
    --   H z - 1 = z^2 * ∫ 0..1 s * (H*(r ...))
    simpa [g, r, Hfun] using
      (EulerBasel.eventually_coreWeighted_of_stepC_core
        (b := b) (F := F)
        (hnear := hnear) (hFdiff := hFdiff) (hFne := hFne)
        (hcore := hcore0))

  --------------------------------------------------------------------
  -- Step D: Convert the weighted core identity + hI into the quadratic quotient tendsto.
  --------------------------------------------------------------------
  -- The Step D lemma expects the weighted integral tends to 0 on the punctured filter.
  -- We already have `hI` (with the same g).
  have hI0 :
      Tendsto
        (fun z : ℂ => ∫ s : ℝ in 0..1, (s : ℂ) * g ((s : ℂ) * z))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (0 : ℂ)) := by
    -- The weighted segment-integral lemma is already stated with `(0..1)` in this file’s `hI`.
    -- Convert to `0..1` if necessary later; for now we reuse it.
    simpa using hI

  -- Finally apply Step D lemma (now imported).
  simpa [b, hb] using
    (EulerBasel.tendsto_quadratic_remainder_div_stepD
      (b := b)
      (eulerLimitFun0 := eulerLimitFun0)
      (H0 := H0)
      (Hfun := Hfun)
      (g := g)
      (hH0_def := hH0_def)
      (hH0_eq_Hfun := by
        intro z hz0
        exact hH0_eq_Hfun (w := z) hz0)
      (hcoreWeighted := hcoreWeighted)
      (hI := hI0))

end

end EulerBasel
