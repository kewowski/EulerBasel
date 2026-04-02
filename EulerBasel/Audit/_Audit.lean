/-
Audit module.

This file is not part of the mathematical development.
It prints key theorem types and reports axiom dependencies for artifact verification purposes.
-/

import EulerBasel.BaselEuler
import EulerBasel.CoefficientProductSide
import EulerBasel.CoefficientSineSide

namespace EulerBasel

-- 1) Final theorem statements (type-check only).
#check baselSum_eq_pi_sq_div_six
#check tsum_eulerTermR_eq_pi_sq_div_six

-- 2) Axiom footprint for the final theorems.
#print axioms baselSum_eq_pi_sq_div_six
#print axioms tsum_eulerTermR_eq_pi_sq_div_six

-- 3) Axiom footprint for the two coefficient-interface expansions.
#check sinDivPiZ0_sub_one_sub_baselSum_isLittleO
#check sinDivPiZ0_sub_quadratic_isLittleO
#print axioms sinDivPiZ0_sub_one_sub_baselSum_isLittleO
#print axioms sinDivPiZ0_sub_quadratic_isLittleO

end EulerBasel