/-
EulerBasel/CoefficientEulerLogDeriv.lean

Log-derivative convergence on the punctured neighborhood.

On `nearZeroPunctured`, the logarithmic derivatives of the Euler partial products
converge to the logarithmic derivative of the Euler limit function.
-/

import EulerBasel.CoefficientEulerLicensing

namespace EulerBasel

open scoped Topology
open Filter

theorem tendsto_logDeriv_eulerProd :
  ∀ z ∈ nearZeroPunctured,
    Tendsto (fun N => logDeriv (fun w : ℂ => eulerProd w N) z)
      atTop
      (𝓝 (logDeriv eulerLimitFun z)) := by
  intro z hz

  have hne : eulerLimitFun z ≠ 0 :=
    eulerLimitFun_ne_zero_of_mem_nearZeroPunctured (z := z) hz

  simpa using
    (Complex.logDeriv_tendsto
      (s := nearZeroPunctured)
      isOpen_nearZeroPunctured
      hz
      tendstoLocallyUniformlyOn_eulerProd_nearZeroPunctured
      eventually_differentiableOn_eulerProd_nearZeroPunctured
      hne)

end EulerBasel

