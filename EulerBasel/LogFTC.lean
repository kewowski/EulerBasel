import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology Interval
open Filter

namespace EulerBasel
noncomputable section

/-
ScratchLogFTC.lean

Local calculus for the integrating factor
  H(w) = F(w) * exp(b * w^2)
and its derivative identity in terms of
  r(w) = (logDeriv F w + (2*b)*w) / w.

Important: in this mathlib snapshot, `hasDerivAt_exp` is for `NormedSpace.exp`,
so we use `NormedSpace.exp` (not `Complex.exp`).
-/

-- Using QuadraticReconstruction’s notation:
variable (b : ℂ) (F : ℂ → ℂ)

def r (w : ℂ) : ℂ := (logDeriv F w + (2 * b) * w) / w
def H (w : ℂ) : ℂ := F w * NormedSpace.exp (b * w ^ 2)

/-- Derivative of `u ↦ b * u^2` is `2*b*u`. -/
lemma hasDerivAt_b_mul_sq (w : ℂ) :
    HasDerivAt (fun u : ℂ => b * u ^ 2) (2 * b * w) w := by
  have hpow : HasDerivAt (fun u : ℂ => u ^ 2) (2 * w) w := by
    simpa using (hasDerivAt_pow (n := 2) (x := w))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hpow.const_mul b

/-- Derivative of `u ↦ exp(b*u^2)` is `exp(b*w^2) * (2*b*w)`. -/
lemma hasDerivAt_exp_b_mul_sq (w : ℂ) :
    HasDerivAt (fun u : ℂ => NormedSpace.exp (b * u ^ 2))
      (NormedSpace.exp (b * w ^ 2) * (2 * b * w)) w := by
  have hinner : HasDerivAt (fun u : ℂ => b * u ^ 2) (2 * b * w) w :=
    hasDerivAt_b_mul_sq (b := b) w
  have hexp :
      HasDerivAt NormedSpace.exp (NormedSpace.exp (b * w ^ 2)) (b * w ^ 2) := by
    simpa using (hasDerivAt_exp (x := (b * w ^ 2)))
  simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using hexp.comp w hinner

/-- Convenience: `deriv (u ↦ exp(b*u^2)) w = exp(b*w^2) * (2*b*w)`. -/
lemma deriv_exp_b_mul_sq (w : ℂ) :
    deriv (fun u : ℂ => NormedSpace.exp (b * u ^ 2)) w
      = NormedSpace.exp (b * w ^ 2) * (2 * b * w) := by
  simpa using (hasDerivAt_exp_b_mul_sq (b := b) w).deriv

/-- Compute `deriv H` in terms of `r`. -/
lemma deriv_H_eq (w : ℂ)
    (hw0 : w ≠ 0)
    (hF : DifferentiableAt ℂ F w)
    (hF0 : F w ≠ 0) :
    deriv (H (b := b) (F := F)) w
      = (H (b := b) (F := F) w) * (w * r (b := b) (F := F) w) := by
  have hE : DifferentiableAt ℂ (fun u : ℂ => NormedSpace.exp (b * u ^ 2)) w := by
    exact (hasDerivAt_exp_b_mul_sq (b := b) w).differentiableAt

  have hmul :
      deriv (fun u : ℂ => F u * NormedSpace.exp (b * u ^ 2)) w
        = deriv F w * NormedSpace.exp (b * w ^ 2)
          + F w * deriv (fun u : ℂ => NormedSpace.exp (b * u ^ 2)) w := by
    simpa using
      (deriv_mul (x := w) (c := F) (d := fun u : ℂ => NormedSpace.exp (b * u ^ 2)) hF hE)

  have hlog : deriv F w = logDeriv F w * F w := by
    have : logDeriv F w * F w = (deriv F w / F w) * F w := by
      simp [logDeriv_apply]
    simpa [div_eq_mul_inv, mul_assoc, hF0] using this.symm

  have hEder :
      deriv (fun u : ℂ => NormedSpace.exp (b * u ^ 2)) w
        = NormedSpace.exp (b * w ^ 2) * (2 * b * w) :=
    deriv_exp_b_mul_sq (b := b) w

  -- Key rewrite: only cancel `w` (never cancel `F w * exp(...)`).
  have hw_mul_div :
      w * ((logDeriv F w + (2 * b) * w) / w) = (logDeriv F w + (2 * b) * w) := by
    -- Do the cancellation explicitly (avoid simp getting stuck on normal forms like `2 * (b*w)`).
    set A : ℂ := logDeriv F w + (2 * b) * w
    calc
      w * (A / w) = w * (A * w⁻¹) := by
        simp [A, div_eq_mul_inv]
      _ = w * (w⁻¹ * A) := by
        -- commute to bring `w⁻¹` next to `w`
        simp [mul_comm]
      _ = (w * w⁻¹) * A := by
        simp [mul_assoc]
      _ = A := by
        simp [hw0, A]

  calc
    deriv (H (b := b) (F := F)) w
        = deriv F w * NormedSpace.exp (b * w ^ 2)
          + F w * deriv (fun u : ℂ => NormedSpace.exp (b * u ^ 2)) w := by
            simpa [H] using hmul
    _ = (logDeriv F w * F w) * NormedSpace.exp (b * w ^ 2)
          + F w * (NormedSpace.exp (b * w ^ 2) * (2 * b * w)) := by
            simp [hlog, hEder]
    _ = (F w * NormedSpace.exp (b * w ^ 2)) * (logDeriv F w + (2 * b) * w) := by
            ring
    _ = (F w * NormedSpace.exp (b * w ^ 2)) * (w * ((logDeriv F w + (2 * b) * w) / w)) := by
            -- rewrite the factor using `hw_mul_div`
            simp [hw_mul_div]
    _ = (H (b := b) (F := F) w) * (w * r (b := b) (F := F) w) := by
            simp [H, r, mul_assoc, mul_left_comm, mul_comm]

end

end EulerBasel
