/-
EulerBasel/CoefficientSineSide.lean

Sine-side quadratic expansion for sinDivPiZ0:
  sinDivPiZ0 z = 1 - (piC^2/6) z^2 + o(z^2) as z → 0.
-/

import EulerBasel.CoefficientDefs
import EulerBasel.SinDivZExpansion
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic  -- for `field_simp`

noncomputable section
open Classical
open scoped Topology BigOperators Asymptotics
open Filter
open Asymptotics

namespace EulerBasel

-- π as a complex number (local convenience).
local notation "piC" => ((Real.pi : ℝ) : ℂ)

/-- A 0-patched quadratic remainder for `sinDivPiZ0`. -/
def sinDivPiZ0_sub_quadratic_remainder (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    sinDivPiZ0 z - ((1 : ℂ) - (piC ^ 2 / 6 : ℂ) * z ^ 2)

/-- Pointwise identification with `sin_div_id_sub_quadratic_remainder (piC*z)`. -/
lemma sinDivPiZ0_sub_quadratic_remainder_eq (z : ℂ) :
    sinDivPiZ0_sub_quadratic_remainder z
      = sin_div_id_sub_quadratic_remainder (piC * z) := by
  by_cases hz : z = 0
  · subst hz
    simp [sinDivPiZ0_sub_quadratic_remainder, sin_div_id_sub_quadratic_remainder]
  ·
    have hpi : (piC : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hpiz : (piC * z : ℂ) ≠ 0 := mul_ne_zero hpi hz
    simp [sinDivPiZ0_sub_quadratic_remainder, sin_div_id_sub_quadratic_remainder,
      sinDivPiZ0, hz, hpiz, sinDivPiZ]
    ring_nf

/-- The π-scaled quadratic remainder is `o(z^2)` as `z → 0`. -/
theorem sinDivPiZ0_sub_quadratic_isLittleO :
    (fun z : ℂ => sinDivPiZ0 z - ((1 : ℂ) - (piC ^ 2 / 6 : ℂ) * z ^ 2))
      =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
  classical
  -- Define the scaling map explicitly.
  let mulPi : ℂ → ℂ := fun z => piC * z

  have hmulPi : Tendsto mulPi (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa [mulPi] using
      (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 0) (𝓝 0)))

  -- Compose the already-proved little-o for `sin z / z` with `mulPi`.
  have hcomp :
      (fun z : ℂ => sin_div_id_sub_quadratic_remainder (mulPi z))
        =o[𝓝 (0 : ℂ)] (fun z : ℂ => (mulPi z) ^ 2) := by
    simpa [mulPi] using (sin_div_id_sub_quadratic_isLittleO.comp_tendsto hmulPi)

  -- Rewrite to our patched remainder.
  have hrem :
      (fun z : ℂ => sinDivPiZ0_sub_quadratic_remainder z)
        =o[𝓝 (0 : ℂ)] (fun z : ℂ => (mulPi z) ^ 2) := by
    simpa [sinDivPiZ0_sub_quadratic_remainder_eq, mulPi] using hcomp

  have hpi : (piC : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero

  -- side condition for `isLittleO_iff_tendsto` with `g(z)=(piC*z)^2`
  have hzero_g :
      ∀ z : ℂ, ((mulPi z) ^ 2 = 0) → sinDivPiZ0_sub_quadratic_remainder z = 0 := by
    intro z hz
    have hz0 : z = 0 := by
      have : (mulPi z : ℂ) = 0 := by
        by_contra h
        exact (pow_ne_zero 2 h) hz
      have : (piC : ℂ) * z = 0 := by simpa [mulPi] using this
      exact (mul_eq_zero.mp this).resolve_left hpi
    subst hz0
    simp [sinDivPiZ0_sub_quadratic_remainder]

  have hiff_g :=
    Asymptotics.isLittleO_iff_tendsto
      (f := fun z : ℂ => sinDivPiZ0_sub_quadratic_remainder z)
      (g := fun z : ℂ => (mulPi z) ^ 2)
      (l := 𝓝 (0 : ℂ)) hzero_g

  have ht_g :
      Tendsto (fun z : ℂ => sinDivPiZ0_sub_quadratic_remainder z / (mulPi z) ^ 2)
        (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    (hiff_g.1 hrem)

  -- Convert quotient wrt `(mulPi z)^2` to quotient wrt `z^2`.
  have ht :
      Tendsto (fun z : ℂ => sinDivPiZ0_sub_quadratic_remainder z / (z ^ 2))
        (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hpi2 : (piC ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hpi

    have hquot :
        (fun z : ℂ => sinDivPiZ0_sub_quadratic_remainder z / (z ^ 2))
          =
        (fun z : ℂ => (piC ^ 2) * (sinDivPiZ0_sub_quadratic_remainder z / ((mulPi z) ^ 2))) := by
      funext z
      by_cases hz : z = 0
      · subst hz
        simp [sinDivPiZ0_sub_quadratic_remainder, mulPi]
      ·
        have hz2 : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hz
        have hpiz : (mulPi z : ℂ) ≠ 0 := mul_ne_zero hpi hz
        have hpiz2 : ((mulPi z) ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hpiz
        have hden : (mulPi z) ^ 2 = (piC ^ 2) * (z ^ 2) := by
          simp [mulPi]
          ring_nf

        have this :
            sinDivPiZ0_sub_quadratic_remainder z / (z ^ 2)
              = (piC ^ 2) * (sinDivPiZ0_sub_quadratic_remainder z / (mulPi z) ^ 2) := by
          field_simp [div_eq_mul_inv, hz2, hpiz2]
          calc
            sinDivPiZ0_sub_quadratic_remainder z * (mulPi z) ^ 2
                = sinDivPiZ0_sub_quadratic_remainder z * ((piC ^ 2) * z ^ 2) := by
                    simp [hden]
            _   = sinDivPiZ0_sub_quadratic_remainder z * (z ^ 2) * (piC ^ 2) := by
                    simp [mul_assoc, mul_comm]

        exact this

    have ht_mul :
        Tendsto
          (fun z : ℂ => (piC ^ 2) * (sinDivPiZ0_sub_quadratic_remainder z / (mulPi z) ^ 2))
          (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using (tendsto_const_nhds.mul ht_g)

    simpa [hquot] using ht_mul

  -- Package back to the unpatched expression.
  have hzero_z2 :
      ∀ z : ℂ, (z ^ 2 = 0) →
        (sinDivPiZ0 z - ((1 : ℂ) - (piC ^ 2 / 6 : ℂ) * z ^ 2)) = 0 := by
    intro z hz2
    have hz0 : z = 0 := by
      by_contra h
      exact (pow_ne_zero 2 h) hz2
    subst hz0
    simp [sinDivPiZ0]

  have hiff :=
    Asymptotics.isLittleO_iff_tendsto
      (f := fun z : ℂ => sinDivPiZ0 z - ((1 : ℂ) - (piC ^ 2 / 6 : ℂ) * z ^ 2))
      (g := fun z : ℂ => z ^ 2)
      (l := 𝓝 (0 : ℂ)) hzero_z2

  have hqeq :
      (fun z : ℂ =>
          (sinDivPiZ0 z - ((1 : ℂ) - (piC ^ 2 / 6 : ℂ) * z ^ 2)) / (z ^ 2))
        =
      (fun z : ℂ => sinDivPiZ0_sub_quadratic_remainder z / (z ^ 2)) := by
    funext z
    by_cases hz : z = 0
    · subst hz
      simp [sinDivPiZ0_sub_quadratic_remainder, sinDivPiZ0]
    · simp [sinDivPiZ0_sub_quadratic_remainder, hz]

  exact hiff.2 (by simpa [hqeq] using ht)

end EulerBasel
