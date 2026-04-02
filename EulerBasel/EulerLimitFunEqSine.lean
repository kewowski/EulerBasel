/-
EulerBasel/EulerLimitFunEqSine.lean

Bridge lemma: on `nearZeroPunctured`, the licensed limit function `eulerLimitFun`
agrees with the normalized sine function `sinDivPiZ0`.

Snapshot-friendly: no pointwise `Tendsto` extraction.
We prove the bridge by unfolding definitions on `z ≠ 0`.
-/

import EulerBasel.CoefficientEulerLicensing
import EulerBasel.CoefficientDefs

namespace EulerBasel

noncomputable section

open scoped Topology
open Filter

/--
On `nearZeroPunctured`, `eulerLimitFun z = sinDivPiZ0 z`.

This is definitional, modulo the `0`-patch in `sinDivPiZ0`.
-/
theorem eulerLimitFun_eq_sinDivPiZ0_of_mem_nearZeroPunctured {z : ℂ}
    (hz : z ∈ nearZeroPunctured) :
    eulerLimitFun z = sinDivPiZ0 z := by
  have hz0 : z ≠ 0 := hz.2
  -- Unfold `eulerLimitFun`, then reduce `sinDivPiZ0` using `hz0`,
  -- then unfold `sinDivPiZ`.
  simp [eulerLimitFun, sinDivPiZ0, hz0, sinDivPiZ]

end

end EulerBasel
