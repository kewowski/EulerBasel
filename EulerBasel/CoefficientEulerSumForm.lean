/-
EulerBasel/CoefficientEulerSumForm.lean

Finite Euler step:
rewrite the logarithmic derivative of the finite Euler product as a finite sum,
then rewrite each summand into Euler’s rational form.
-/

import EulerBasel.Coefficient
import EulerBasel.CoefficientEulerLicensing
import EulerBasel.CoefficientEulerLogDeriv

namespace EulerBasel

open scoped Topology
open scoped BigOperators
open Filter

/-- Each Euler factor is differentiable everywhere. -/
lemma differentiableAt_eulerFactor (m : ℕ) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => eulerFactor w m) z := by
  simp [eulerFactor]

/--
A small algebra lemma used to avoid `simp` loops at the end.

This is valid without hypotheses because inverses in `ℂ` are total (`0⁻¹ = 0`).
-/
lemma neg_two_mul_inv_sub_eq_two_mul_inv_sub_swap (z a : ℂ) :
    -(2 * z * (a - z ^ 2)⁻¹) = 2 * z * (z ^ 2 - a)⁻¹ := by
  by_cases h0 : a - z ^ 2 = 0
  ·
    have hz : z ^ 2 - a = 0 := by
      have : a = z ^ 2 := sub_eq_zero.mp h0
      simp [this]
    simp [h0, hz]
  ·
    have h1 : z ^ 2 - a ≠ 0 := by
      intro hz0
      apply h0
      have : z ^ 2 = a := sub_eq_zero.mp hz0
      simp [this]
    (field_simp [h0, h1]; ring)

/--
Closed form for the log-derivative of one Euler factor, under the natural
nonvanishing hypothesis at the evaluation point.
-/
lemma logDerivC_eulerFactor_eq_of_ne (m : ℕ) (z : ℂ) (hne : eulerFactor z m ≠ 0) :
    logDerivC (fun w : ℂ => eulerFactor w m) z
      = (2 * z) / (z ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2) := by
  classical
  set a : ℂ := ((m : ℂ) + 1) ^ 2

  have hm : (m : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero m)

  have ha : a ≠ 0 := by
    simpa [a] using (pow_ne_zero 2 hm)

  have hNF :
      logDerivC (fun w : ℂ => eulerFactor w m) z
        =
      -(2 * z * a⁻¹ * (1 + -(z ^ 2 * a⁻¹))⁻¹) := by
    simp [logDerivC, eulerFactor, a, div_eq_mul_inv, sub_eq_add_neg]

  have hRHS :
      (2 * z) / (z ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2)
        =
      2 * z * (z ^ 2 - a)⁻¹ := by
    simp [div_eq_mul_inv, a, sub_eq_add_neg]

  rw [hNF, hRHS]

  by_cases hza : z ^ 2 - a = 0
  ·
    have hz2 : z ^ 2 = a := sub_eq_zero.mp hza
    have hzero : eulerFactor z m = 0 := by
      calc
        eulerFactor z m
            = 1 - z ^ 2 * a⁻¹ := by
                simp [eulerFactor, a, div_eq_mul_inv, sub_eq_add_neg]
        _   = 1 - a * a⁻¹ := by simp [hz2]
        _   = 1 - 1 := by simp [ha]
        _   = 0 := by ring
    exact (hne hzero).elim
  ·
    have hb : a - z ^ 2 ≠ 0 := by
      intro hb0
      apply hza
      have : z ^ 2 - a = -(a - z ^ 2) := by ring
      simp [this, hb0]

    have inner_ne : (1 + -(z ^ 2 * a⁻¹)) ≠ 0 := by
      intro hin
      have hin' : 1 - (z ^ 2 * a⁻¹) = 0 := by
        simpa [sub_eq_add_neg] using hin
      have hmul : (1 - (z ^ 2 * a⁻¹)) * a = 0 := by
        have h := congrArg (fun t => t * a) hin'
        calc
          (1 - (z ^ 2 * a⁻¹)) * a = (0 : ℂ) * a := h
          _ = 0 := by simp
      have hleft : (1 - (z ^ 2 * a⁻¹)) * a = a - z ^ 2 := by
        simp [sub_eq_add_neg, add_mul, ha]
      have : a - z ^ 2 = 0 := by
        calc
          a - z ^ 2 = (1 - (z ^ 2 * a⁻¹)) * a := by simpa using hleft.symm
          _ = 0 := hmul
      exact hb this

    have inner_ne' : (1 - (z ^ 2 * a⁻¹)) ≠ 0 := by
      intro hin'
      apply inner_ne
      simpa [sub_eq_add_neg] using hin'

    have key :
        a⁻¹ * (1 + -(z ^ 2 * a⁻¹))⁻¹ = (a - z ^ 2)⁻¹ := by
      have key' :
          a⁻¹ * (1 - (z ^ 2 * a⁻¹))⁻¹ = (a - z ^ 2)⁻¹ := by
        field_simp [ha, hb, inner_ne']
      simpa [sub_eq_add_neg] using key'

    have h1 :
        -(2 * z * a⁻¹ * (1 + -(z ^ 2 * a⁻¹))⁻¹)
          =
        -(2 * z * (a - z ^ 2)⁻¹) := by
      simpa [mul_assoc] using congrArg (fun t => -(2 * z * t)) key

    exact h1.trans (neg_two_mul_inv_sub_eq_two_mul_inv_sub_swap (z := z) (a := a))

/--
Product-to-sum for `logDerivC` on the finite Euler product written explicitly as a `Finset.prod`,
supplying the hypotheses expected by `logDerivC_finset_prod`.
-/
lemma logDerivC_finprod_eulerFactor_eq_sum (N : ℕ) (z : ℂ)
    (hne : ∀ i < N, eulerFactor z i ≠ 0) :
    logDerivC (fun w : ℂ => ∏ i ∈ Finset.range N, eulerFactor w i) z
      =
    ∑ i ∈ Finset.range N, logDerivC (fun w : ℂ => eulerFactor w i) z := by
  classical
  simpa using
    (logDerivC_finset_prod
      (s := Finset.range N)
      (f := fun i (w : ℂ) => eulerFactor w i)
      (z := z)
      (by
        intro i hi
        have : i < N := Finset.mem_range.mp hi
        simpa using differentiableAt_eulerFactor (m := i) (z := z))
      (by
        intro i hi
        have : i < N := Finset.mem_range.mp hi
        exact (hne i this)))

/--
Same finite identity, but with Euler’s rational form in the summand.
-/
lemma logDerivC_finprod_eulerFactor_eq_sum_rational (N : ℕ) (z : ℂ)
    (hne : ∀ i < N, eulerFactor z i ≠ 0) :
    logDerivC (fun w : ℂ => ∏ i ∈ Finset.range N, eulerFactor w i) z
      =
    ∑ i ∈ Finset.range N, (2 * z) / (z ^ 2 - ((i + 1 : ℕ) : ℂ) ^ 2) := by
  classical
  have hsum := logDerivC_finprod_eulerFactor_eq_sum (N := N) (z := z) hne
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < N := Finset.mem_range.mp hi
  have hne_i : eulerFactor z i ≠ 0 := hne i hi'
  simpa using (logDerivC_eulerFactor_eq_of_ne (m := i) (z := z) hne_i)

end EulerBasel
