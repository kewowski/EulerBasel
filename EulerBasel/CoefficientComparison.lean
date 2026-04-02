/-
EulerBasel/CoefficientComparison.lean

Final Euler-style coefficient comparison layer.

Structure (Euler spirit):
1) Sine-side: sinDivPiZ0 = 1 - (piC^2/6) z^2 + o(z^2)
2) Product-side: sinDivPiZ0 = 1 - baselSum z^2 + o(z^2)
3) Uniqueness of quadratic coefficient: baselSum = (piC^2)/6
4) Real corollary
-/

import EulerBasel.CoefficientDefs
import EulerBasel.CoefficientSineSide
import EulerBasel.CoefficientProductSide
import EulerBasel.QuadraticCoefficient
import EulerBasel.EulerSumLimit

noncomputable section
open Classical
open scoped Topology BigOperators Asymptotics
open Filter
open Asymptotics

namespace EulerBasel

-- π as a complex number (local convenience).
local notation "piC" => ((Real.pi : ℝ) : ℂ)

/-- The Basel identity in the project’s complex indexing: `∑ 1/(n+1)^2 = π^2/6`. -/
theorem baselSum_eq_pi_sq_div_six :
    baselSum = (piC ^ 2) / 6 := by
  have ha :
      (fun z : ℂ => sinDivPiZ0 z - ((1 : ℂ) - baselSum * z ^ 2))
        =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
    -- product-side expansion (from CoefficientProductSide)
    simpa using sinDivPiZ0_sub_one_sub_baselSum_isLittleO

  have hb :
      (fun z : ℂ => sinDivPiZ0 z - ((1 : ℂ) - ((piC ^ 2) / 6) * z ^ 2))
        =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
    -- sine-side expansion (from CoefficientSineSide)
    simpa using sinDivPiZ0_sub_quadratic_isLittleO

  have h :=
    quadratic_coeff_unique (f := sinDivPiZ0) (a := baselSum) (b := (piC ^ 2) / 6) ha hb
  simpa using h

/-- Real-valued corollary: the real Basel sum is `π^2/6`. -/
theorem tsum_eulerTermR_eq_pi_sq_div_six :
    (∑' n : ℕ, eulerTermR n : ℝ) = Real.pi ^ 2 / 6 := by
  have hC : baselSum = (piC ^ 2) / 6 := by
    simpa using baselSum_eq_pi_sq_div_six

  -- First identify the complex `tsum` of the real summands with `baselSum`.
  have htsumC : (∑' n : ℕ, (eulerTermR n : ℂ)) = baselSum := by
    -- from EulerSumLimit: the complex series of coerced real terms sums to `baselSum`
    -- baselSum = tsum baselTerm = tsum eulerTerm, and eulerTerm n = (eulerTermR n : ℂ).
    have hsC : Summable (fun n : ℕ => (eulerTermR n : ℂ)) :=
      (EulerBasel.hasSum_eulerTermR_coe).summable
    have hs : Summable (fun n : ℕ => eulerTerm n) := by
      refine hsC.congr ?_
      intro n
      simpa using (EulerBasel.eulerTerm_eq_ofReal n).symm

    have htsum_eq :
        (∑' n : ℕ, (eulerTermR n : ℂ)) = (∑' n : ℕ, eulerTerm n) := by
      refine tsum_congr ?_
      intro n
      simpa using (EulerBasel.eulerTerm_eq_ofReal n).symm

    have hbas : baselSum = (∑' n : ℕ, eulerTerm n) :=
      EulerBasel.baselSum_eq_tsum_eulerTerm

    simpa [hbas] using htsum_eq


  -- Now cast the real `tsum` to ℂ and rewrite it as the complex `tsum` of coerced terms.
  have hcomplex :
      ((∑' n : ℕ, eulerTermR n : ℝ) : ℂ) = (piC ^ 2) / 6 := by
    calc
      ((∑' n : ℕ, eulerTermR n : ℝ) : ℂ)
          = (∑' n : ℕ, (eulerTermR n : ℂ)) := by
              -- `ofReal` commutes with `tsum`
              simpa using (Complex.ofReal_tsum (fun n : ℕ => eulerTermR n))
      _   = baselSum := htsumC
      _   = (piC ^ 2) / 6 := hC

  -- Convert RHS to a coerced real, then use `ofReal_inj`.
  have hcomplex' :
      ((∑' n : ℕ, eulerTermR n : ℝ) : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    -- `piC` is notation, so this is just `simp` on coercions/powers.
    simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomplex

  exact Complex.ofReal_inj.mp hcomplex'

end EulerBasel





