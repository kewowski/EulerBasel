/-
EulerBasel/SinDivZExpansion.lean

Derive the quadratic expansion of (sin z)/z near 0 from the cubic expansion of sin z.

Input from EulerBasel.SinCubic:
  tendsto_sin_sub_id_div_cubic :
    Tendsto (fun z : ℂ => (Complex.sin z - z) / z^3) (𝓝[≠] 0) (𝓝 (-(1/6 : ℂ))).
-/

import EulerBasel.SinCubic

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs

open scoped Topology BigOperators Asymptotics
open Filter Asymptotics

namespace EulerBasel

noncomputable section

/-- 0-patched quadratic remainder for `sin z / z` near 0. -/
def sin_div_id_sub_quadratic_remainder (z : ℂ) : ℂ :=
  if z = 0 then 0 else (Complex.sin z / z) - (1 - (1 / 6 : ℂ) * z ^ 2)

/-- Algebra on `z ≠ 0`: `((sin z - z)/z^3) * z^2 = (sin z - z)/z`. -/
lemma sin_sub_id_div_cubic_mul_sq_eq_div (z : ℂ) (hz : z ≠ 0) :
    ((Complex.sin z - z) / z ^ 3) * z ^ 2 = (Complex.sin z - z) / z := by
  field_simp [hz]
  try ring

/-- On `z ≠ 0`, `sin z / z = 1 + (sin z - z) / z`. -/
lemma sin_div_id_eq_one_add_sin_sub_id_div (z : ℂ) (hz : z ≠ 0) :
    Complex.sin z / z = (1 : ℂ) + (Complex.sin z - z) / z := by
  have : Complex.sin z / z = z / z + (Complex.sin z - z) / z := by
    field_simp [hz]
    try ring
  simpa [div_self hz, add_assoc, add_left_comm, add_comm] using this

/-- Punctured limit: `sin z / z → 1` as `z → 0`, `z ≠ 0`. -/
theorem tendsto_sin_div_id_punctured_one :
    Tendsto (fun z : ℂ => Complex.sin z / z) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  let f : ℂ → ℂ := fun z => (Complex.sin z - z) / z ^ 3
  let g : ℂ → ℂ := fun z => z ^ 2

  have hf : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (-(1 / 6 : ℂ))) := by
    simpa [f] using
      (tendsto_sin_sub_id_div_cubic :
        Tendsto (fun z : ℂ => (Complex.sin z - z) / z ^ 3) (𝓝[≠] (0 : ℂ)) (𝓝 (-(1 / 6 : ℂ))))

  have hz : Tendsto (fun z : ℂ => z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    (tendsto_id).mono_left nhdsWithin_le_nhds

  have hg : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa [g] using (hz.pow 2)

  have hmul : Tendsto (fun z : ℂ => f z * g z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa using (Filter.Tendsto.mul hf hg)

  have hdiv : Tendsto (fun z : ℂ => (Complex.sin z - z) / z) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz' : z ≠ (0 : ℂ) := by simpa using hz0
    simp [f, g, sin_sub_id_div_cubic_mul_sq_eq_div z hz']

  have hconst : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) :=
    tendsto_const_nhds

  have hone_add :
      Tendsto (fun z : ℂ => (1 : ℂ) + (Complex.sin z - z) / z) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using (Filter.Tendsto.add hconst hdiv)

  refine hone_add.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz0
  have hz' : z ≠ (0 : ℂ) := by simpa using hz0
  simp [sin_div_id_eq_one_add_sin_sub_id_div z hz']

/-- Quadratic little-o statement (0-patched) for `sin z / z`. -/
theorem sin_div_id_sub_quadratic_isLittleO :
    (fun z : ℂ => sin_div_id_sub_quadratic_remainder z) =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
  let q : ℂ → ℂ := fun z => (Complex.sin z - z) / z ^ 3 + (1 / 6 : ℂ)

  -- q → 0 on punctured
  have hf : Tendsto (fun z : ℂ => (Complex.sin z - z) / z ^ 3)
      (𝓝[≠] (0 : ℂ)) (𝓝 (-(1 / 6 : ℂ))) := by
    simpa using
      (tendsto_sin_sub_id_div_cubic :
        Tendsto (fun z : ℂ => (Complex.sin z - z) / z ^ 3) (𝓝[≠] (0 : ℂ)) (𝓝 (-(1 / 6 : ℂ))))

  have hconst : Tendsto (fun _ : ℂ => (1 / 6 : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 6 : ℂ)) :=
    tendsto_const_nhds

  have hq_punct : Tendsto q (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hadd := (Filter.Tendsto.add hf hconst)
    simpa [q] using hadd

  -- patched remainder equals unpatched on punctured
  have hpatch :
      (fun z : ℂ => sin_div_id_sub_quadratic_remainder z)
        =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ => (Complex.sin z / z) - (1 - (1 / 6 : ℂ) * z ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz' : z ≠ (0 : ℂ) := by simpa using hz0
    simp [sin_div_id_sub_quadratic_remainder, hz']

  -- quotient identity on punctured: (unpatched)/(z^2) = q
  have hquot_unpatched :
      (fun z : ℂ => ((Complex.sin z / z) - (1 - (1 / 6 : ℂ) * z ^ 2)) / (z ^ 2))
        =ᶠ[𝓝[≠] (0 : ℂ)] q := by
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz' : z ≠ (0 : ℂ) := by simpa using hz0
    have : ((Complex.sin z / z) - (1 - (1 / 6 : ℂ) * z ^ 2)) / (z ^ 2) = q z := by
      simp [q]
      field_simp [hz']
      ring_nf
    simpa using this

  -- therefore: (patched)/(z^2) =ᶠ q on punctured
  have hquot_patched :
      (fun z : ℂ => sin_div_id_sub_quadratic_remainder z / (z ^ 2))
        =ᶠ[𝓝[≠] (0 : ℂ)] q := by
    filter_upwards [hpatch, hquot_unpatched] with z hzEq1 hzEq2
    simpa [hzEq1] using hzEq2

  -- Tendsto of quotient on punctured is 0 because q → 0
  have ht_punct :
      Tendsto (fun z : ℂ => sin_div_id_sub_quadratic_remainder z / (z ^ 2))
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    refine (hq_punct.congr' ?_)
    exact hquot_patched.symm

  -- side condition for isLittleO_of_tendsto': on punctured, z^2=0 never happens
  have hgf_punct :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), (z ^ 2 = 0 → sin_div_id_sub_quadratic_remainder z = 0) := by
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz' : z ≠ (0 : ℂ) := by simpa using hz0
    intro hz2
    have hz0' : z = 0 := eq_zero_of_pow_eq_zero (n := 2) hz2
    exact (hz' hz0').elim

  have ho_punct :
      (fun z : ℂ => sin_div_id_sub_quadratic_remainder z)
        =o[𝓝[≠] (0 : ℂ)] (fun z : ℂ => z ^ 2) :=
    isLittleO_of_tendsto' (f := fun z : ℂ => sin_div_id_sub_quadratic_remainder z)
      (g := fun z : ℂ => z ^ 2) (l := 𝓝[≠] (0 : ℂ)) hgf_punct ht_punct

  -- Extend the quotient tendsto from punctured to full `nhds` using `pure_sup_nhdsNE`.
  let φ : ℂ → ℂ := fun z => sin_div_id_sub_quadratic_remainder z / (z ^ 2)

  have hφ0 : φ (0 : ℂ) = (0 : ℂ) := by
    simp [φ, sin_div_id_sub_quadratic_remainder]

  have ht0' : Tendsto φ (pure (0 : ℂ)) (𝓝 (φ (0 : ℂ))) :=
    tendsto_pure_nhds φ (0 : ℂ)

  have ht0 : Tendsto φ (pure (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa [hφ0] using ht0'

  have ht_nhds : Tendsto φ (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have ht_sup :
        Tendsto φ (pure (0 : ℂ) ⊔ 𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
      Tendsto.sup ht0 ht_punct
    have hle :
        𝓝 (0 : ℂ) ≤ pure (0 : ℂ) ⊔ 𝓝[≠] (0 : ℂ) :=
      le_of_eq (pure_sup_nhdsNE (0 : ℂ)).symm
    exact ht_sup.mono_left hle

  -- side condition for nhds: z^2=0 -> remainder=0 holds for all z
  have hgf_nhds : ∀ z : ℂ, (z ^ 2 = 0 → sin_div_id_sub_quadratic_remainder z = 0) := by
    intro z hz2
    have hz0 : z = 0 := eq_zero_of_pow_eq_zero (n := 2) hz2
    subst hz0
    simp [sin_div_id_sub_quadratic_remainder]

  exact isLittleO_of_tendsto (f := fun z : ℂ => sin_div_id_sub_quadratic_remainder z)
    (g := fun z : ℂ => z ^ 2) (l := 𝓝 (0 : ℂ)) hgf_nhds ht_nhds

end

end EulerBasel
