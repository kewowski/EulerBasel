/-
EulerBasel/QuadraticReconstruction_FTC.lean

Helper for QuadraticReconstruction.lean:

Build the segment FTC identity for the integrating factor H, using only:
- LogFTC (derivative + segment derivative plumbing)
- NearZeroSegment (segment stays in nearZeroPunctured)
- FundThmCalculus FTC lemma variants
-/

import EulerBasel.LogFTC
import EulerBasel.NearZeroSegment

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology Interval
open Filter

namespace EulerBasel
noncomputable section

/--
FTC identity on `[0,1]` for the integrating factor along the segment `s ↦ (s:ℂ)*z`.

We use `integral_eq_sub_of_hasDerivAt_of_tendsto` to avoid needing a derivative at the endpoint `s=0`,
and we allow an explicit left endpoint value `fa` supplied via a right-limit hypothesis.

In the main reconstruction we will set `fa = 1`.
-/
lemma segmentFTC_H_eq
    (b : ℂ) (F : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ nearZeroPunctured)
    (hFdiff : ∀ {w : ℂ}, w ∈ nearZeroPunctured → DifferentiableAt ℂ F w)
    (hint :
      IntervalIntegrable
        (fun s : ℝ =>
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
        MeasureTheory.volume (0 : ℝ) (1 : ℝ))
    (fa : ℂ)
    -- endpoint values supplied by one-sided limits
    (h0 :
      Tendsto
        (fun s : ℝ => H (b := b) (F := F) ((s : ℂ) * z))
        (𝓝[>] (0 : ℝ))
        (𝓝 fa))
    (h1 :
      Tendsto
        (fun s : ℝ => H (b := b) (F := F) ((s : ℂ) * z))
        (𝓝[<] (1 : ℝ))
        (𝓝 (H (b := b) (F := F) z))) :
    (∫ s : ℝ in (0 : ℝ)..1,
        (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
      =
      (H (b := b) (F := F) z) - fa := by
  -- Derivative hypothesis on the open interval (0,1).
  have hderiv :
      ∀ s ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun t : ℝ => H (b := b) (F := F) ((t : ℂ) * z))
          ((deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs.1

    -- From `Ioo` we get `s ∈ uIcc` (since 0 ≤ 1).
    have hs_uIcc : s ∈ [[(0 : ℝ), (1 : ℝ)]] := by
      have : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      simpa [Set.uIcc,
        min_eq_left (show (0 : ℝ) ≤ 1 by exact zero_le_one),
        max_eq_right (show (0 : ℝ) ≤ 1 by exact zero_le_one)] using this

    -- Segment point stays in nearZeroPunctured for s ≠ 0.
    have hsz : ((s : ℂ) * z) ∈ nearZeroPunctured :=
      segMul_mem_nearZeroPunctured_uIcc (z := z) hz hs_uIcc hs0

    have hF_at : DifferentiableAt ℂ F ((s : ℂ) * z) := hFdiff hsz

    -- Differentiability of the exp factor at the segment point.
    have hE_at :
        DifferentiableAt ℂ (fun u : ℂ => NormedSpace.exp (b * u ^ 2)) ((s : ℂ) * z) := by
      exact (hasDerivAt_exp_b_mul_sq (b := b) (w := ((s : ℂ) * z))).differentiableAt

    -- Hence H is differentiable at the segment point.
    have hH_at : DifferentiableAt ℂ (H (b := b) (F := F)) ((s : ℂ) * z) := by
      -- H(w) = F(w) * exp(b*w^2)
      simpa [H] using hF_at.mul hE_at

    -- ℂ-derivative of H at (s:ℂ)*z.
    have hH_deriv :
        HasDerivAt (H (b := b) (F := F))
          (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) ((s : ℂ) * z) := by
      exact hH_at.hasDerivAt

    -- Chain rule via w ↦ w*z, then restrict to ℝ with `comp_ofReal`.
    have hmulC : HasDerivAt (fun w : ℂ => w * z) z (s : ℂ) := by
      simpa using (hasDerivAt_mul_const z (x := (s : ℂ)))

    have hcompC :
        HasDerivAt (fun w : ℂ => H (b := b) (F := F) (w * z))
          ((deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z) (s : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hH_deriv.comp (s : ℂ) hmulC)

    have hcompR :
        HasDerivAt (fun t : ℝ => H (b := b) (F := F) ((t : ℂ) * z))
          ((deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z) s := by
      simpa [Function.comp] using (HasDerivAt.comp_ofReal (z := s) hcompC)

    exact hcompR

  -- Apply the `of_tendsto` FTC lemma with `fa` and `fb := H z`.
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun t : ℝ => H (b := b) (F := F) ((t : ℂ) * z))
      (f' := fun s : ℝ =>
        (deriv (H (b := b) (F := F)) ((s : ℂ) * z)) * z)
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (hab := by norm_num)
      (hderiv := hderiv)
      (hint := hint)
      (fa := fa)
      (fb := H (b := b) (F := F) z)
      (ha := h0)
      (hb := h1))

end
end EulerBasel

