/-
EulerBasel/CoefficientEulerSumLimit.lean

Pass N → ∞ packaging for the Euler log-derivative along the finite Euler products.

We package the limit statement proved in `CoefficientEulerLogDeriv`, and we also expose
the same limit with the explicit Euler rational finite sum by combining with
`CoefficientEulerSumForm`.

This file avoids fragile norm lemmas. Instead, it proves factor nonvanishing on
`nearZeroPunctured` by reducing to membership in `Complex.integerComplement`.
-/

import EulerBasel.CoefficientEulerLogDeriv
import EulerBasel.CoefficientEulerSumForm

namespace EulerBasel

open scoped Topology BigOperators
open Filter

noncomputable section

/-- The packaged Euler partial object at stage `N`, the logarithmic derivative of the finite Euler product. -/
def eulerRationalPartial (N : ℕ) (z : ℂ) : ℂ :=
  logDeriv (fun w : ℂ => eulerProd w N) z

/-- Euler partials converge to the log-derivative of the limit function on `nearZeroPunctured`. -/
theorem tendsto_eulerRationalPartial :
    ∀ z ∈ nearZeroPunctured,
      Tendsto (fun N => eulerRationalPartial N z) atTop (nhds (logDeriv eulerLimitFun z)) := by
  intro z hz
  dsimp [eulerRationalPartial]
  exact tendsto_logDeriv_eulerProd (z := z) hz

/--
Rewrite the packaged Euler partial into Euler’s explicit finite rational sum,
under the natural nonvanishing hypothesis on the factors.
-/
theorem eulerRationalPartial_eq_sum_rational (N : ℕ) (z : ℂ)
    (hne : ∀ i < N, eulerFactor z i ≠ 0) :
    eulerRationalPartial N z
      =
    ∑ i ∈ Finset.range N, (2 * z) / (z ^ 2 - ((i + 1 : ℕ) : ℂ) ^ 2) := by
  classical
  have h :=
    logDerivC_finprod_eulerFactor_eq_sum_rational (N := N) (z := z) hne
  have h' :
      deriv (fun w : ℂ => ∏ i ∈ Finset.range N, eulerFactor w i) z
          / ∏ i ∈ Finset.range N, eulerFactor z i
        =
      ∑ i ∈ Finset.range N, (2 * z) / (z ^ 2 - ((i + 1 : ℕ) : ℂ) ^ 2) := by
    simpa [logDerivC, logDeriv, eulerProd] using h
  dsimp [eulerRationalPartial, logDeriv]
  exact h'

/--
Nonvanishing of Euler factors on `nearZeroPunctured`.

If `eulerFactor z i = 0`, then `z = ±(i+1)`, hence `z` is an integer, contradicting
`nearZeroPunctured ⊆ Complex.integerComplement`.
-/
private lemma eulerFactor_ne_zero_of_mem_nearZeroPunctured {z : ℂ}
    (hz : z ∈ nearZeroPunctured) (i : ℕ) :
    eulerFactor z i ≠ 0 := by
  -- reduce to `z ∉ range (fun n : ℤ => (n : ℂ))`
  have hzIC : z ∉ Set.range (fun n : ℤ => (n : ℂ)) := by
    -- `nearZeroPunctured_subset_integerComplement` is in your licensing file
    have : z ∈ Complex.integerComplement :=
      nearZeroPunctured_subset_integerComplement hz
    simpa [Complex.integerComplement] using this

  intro h0

  -- From `eulerFactor z i = 0` derive `z^2 = ((i:ℂ)+1)^2`.
  have hz2 : z ^ 2 = ((i : ℂ) + 1) ^ 2 := by
    have h1 : (1 : ℂ) = z ^ 2 / ((i : ℂ) + 1) ^ 2 := by
      -- `eulerFactor z i = 0` means `1 - z^2/((i+1)^2) = 0`
      have := sub_eq_zero.mp (by simpa [eulerFactor] using h0)
      simpa using this
    have hden : ((i : ℂ) + 1) ^ 2 ≠ 0 := by
      have : (i : ℂ) + 1 ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero i)
      exact pow_ne_zero 2 this
    -- clear denominators
    have hmul : (1 : ℂ) * ((i : ℂ) + 1) ^ 2 = z ^ 2 := (eq_div_iff hden).1 h1
    simpa using hmul.symm

  -- Let `a = (i+1 : ℂ)`. Then `z^2 = a^2` implies `(z-a)(z+a)=0`.
  set a : ℂ := ((i + 1 : ℕ) : ℂ)
  have hza2 : z ^ 2 = a ^ 2 := by
    -- `a = (i:ℂ)+1`
    have : a = (i : ℂ) + 1 := by
      simp [a, Nat.cast_add, Nat.cast_one]
    -- rewrite
    simpa [this] using hz2

  have hzmul0 : (z - a) * (z + a) = 0 := by
    have : (z - a) * (z + a) = z ^ 2 - a ^ 2 := by ring
    calc
      (z - a) * (z + a) = z ^ 2 - a ^ 2 := this
      _ = 0 := by
            -- rewrite `a^2` to `z^2` using `hza2.symm`, then simp
            simp [hza2.symm]

  have hzpm : z - a = 0 ∨ z + a = 0 := mul_eq_zero.mp hzmul0

  -- Convert to “z is an integer”.
  have hz_int : z ∈ Set.range (fun n : ℤ => (n : ℂ)) := by
    rcases hzpm with hza | hza
    · -- z = a
      have hz_eq : z = a := sub_eq_zero.mp hza
      refine ⟨(i + 1 : ℤ), ?_⟩
      simp [a, hz_eq]
    · -- z = -a
      have hz_eq : z = -a := by
        simpa [eq_neg_iff_add_eq_zero] using hza
      refine ⟨-(i + 1 : ℤ), ?_⟩
      simp [a, hz_eq]

  exact hzIC hz_int

/--
Upgraded limit packaging: the explicit Euler rational finite sums converge to the log-derivative
of the limit function on `nearZeroPunctured`.
-/
theorem tendsto_eulerRationalSum :
    ∀ z ∈ nearZeroPunctured,
      Tendsto
        (fun N =>
          ∑ i ∈ Finset.range N, (2 * z) / (z ^ 2 - ((i + 1 : ℕ) : ℂ) ^ 2))
        atTop
        (nhds (logDeriv eulerLimitFun z)) := by
  intro z hz
  have hlim := tendsto_eulerRationalPartial (z := z) hz
  refine hlim.congr' (Filter.Eventually.of_forall ?_)
  intro N
  have hne : ∀ i < N, eulerFactor z i ≠ 0 := by
    intro i hi
    exact eulerFactor_ne_zero_of_mem_nearZeroPunctured (z := z) hz i
  -- rewrite the LHS via the rational-sum identity
  simp [eulerRationalPartial_eq_sum_rational (N := N) (z := z) hne]

end

end EulerBasel
