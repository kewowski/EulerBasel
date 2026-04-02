/-
EulerBasel/EulerLimitFunDeriv.lean

Differentiability API for the Euler product limit function `eulerLimitFun`
on `nearZeroPunctured`.
-/

import EulerBasel.CoefficientDefs
import EulerBasel.TopologyPunctured
import EulerBasel.CoefficientEulerLicensing
import EulerBasel.CoefficientEulerLogDeriv

import Mathlib.Analysis.Asymptotics.Lemmas

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics

namespace EulerBasel

noncomputable section

/--
`eulerLimitFun` is differentiable at any point in `nearZeroPunctured`.
-/
theorem differentiableAt_eulerLimitFun_of_mem_nearZeroPunctured
    {z : ℂ} (hz : z ∈ nearZeroPunctured) :
    DifferentiableAt ℂ eulerLimitFun z := by
  have hz0 : z ≠ 0 := (mem_nearZeroPunctured_iff (z := z)).1 hz |>.2

  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero

  have hden : ((Real.pi : ℂ) * z) ≠ 0 := mul_ne_zero hpi hz0

  have hmul : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) * w) z := by
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) z := by
      set_option linter.unnecessarySimpa false in
      simpa using (differentiableAt_const (c := (Real.pi : ℂ)) (x := z))
    exact hconst.mul differentiableAt_id

  have hsin : DifferentiableAt ℂ Complex.sin ((Real.pi : ℂ) * z) := by
    set_option linter.unnecessarySimpa false in
    simpa using
      (Complex.differentiableAt_sin :
        DifferentiableAt ℂ Complex.sin ((Real.pi : ℂ) * z))

  have hnum :
      DifferentiableAt ℂ (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by
    simpa using hsin.comp z hmul

  set_option linter.unnecessarySimpa false in
  simpa [eulerLimitFun] using hnum.div hmul hden

end

end EulerBasel