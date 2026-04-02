/-
EulerBasel/ProductQuadratic.lean

Finite quadratic expansion for Euler's finite product.

For fixed N, we prove an exact identity
  eulerProd z N = 1 - z^2 * eulerSum N + z^4 * eulerRemainder N z,
and then package
  eulerProd z N - (1 - z^2 * eulerSum N) = o(z^2)  as z → 0.
-/

import EulerBasel.EulerProductExpansion
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic

open scoped Topology BigOperators Asymptotics
open Filter

namespace EulerBasel

noncomputable section

/-- The partial sum `∑_{n < N} 1/(n+1)^2`, using explicit `Finset.sum` to avoid parser issues. -/
def eulerSum (N : ℕ) : ℂ :=
  (Finset.range N).sum (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ 2)

/--
A remainder function `R_N(z)` such that

`eulerProd z N = 1 - z^2 * eulerSum N + z^4 * R_N(z)`.

Defined recursively so it is built from algebraic operations.
-/
def eulerRemainder : ℕ → ℂ → ℂ
  | 0, _ => 0
  | (N + 1), z =>
      let c : ℂ := (1 : ℂ) / ((N : ℂ) + 1) ^ 2
      eulerRemainder N z + eulerSum N * c - z ^ 2 * eulerRemainder N z * c

lemma eulerSum_zero : eulerSum 0 = 0 := by
  simp [eulerSum]

/-- `eulerSum (N+1) = eulerSum N + 1/(N+1)^2` in our `(n:ℂ)+1` indexing. -/
lemma eulerSum_succ (N : ℕ) :
    eulerSum (N + 1) = eulerSum N + (1 : ℂ) / ((N : ℂ) + 1) ^ 2 := by
  classical
  simp [eulerSum, Finset.sum_range_succ, add_comm]

/-- Successor step for the finite product over `Finset.range`. -/
lemma eulerProd_succ (z : ℂ) (N : ℕ) :
    eulerProd z (N + 1) = eulerProd z N * eulerFactor z N := by
  classical
  simp [eulerProd, Finset.prod_range_succ]

/-- A handy rewrite: `z^2 / a = z^2 * a⁻¹`. -/
lemma sq_div_eq_sq_mul_inv (z a : ℂ) : z ^ 2 / a = z ^ 2 * a⁻¹ := by
  simp [div_eq_mul_inv]

/--
Helper: cancel one factor of `z^2` from `z^4 * (z^2)⁻¹`, assuming `z^2 ≠ 0`.

This is written to be robust across snapshots: it avoids calling `mul_inv_cancel`
directly (whose argument order/arity varies across versions), and instead lets
`simp [hz2]` pick the right lemma.
-/
lemma pow_four_mul_inv_pow_two {z : ℂ} (hz2 : z ^ 2 ≠ 0) :
    z ^ 4 * (z ^ 2)⁻¹ = z ^ 2 := by
  have h : z ^ 4 = z ^ 2 * z ^ 2 := by
    ring_nf
  calc
    z ^ 4 * (z ^ 2)⁻¹
        = (z ^ 2 * z ^ 2) * (z ^ 2)⁻¹ := by
            simp [h]
    _   = z ^ 2 * (z ^ 2 * (z ^ 2)⁻¹) := by
            simp [mul_assoc]
    _   = z ^ 2 * 1 := by
            simp [hz2]
    _   = z ^ 2 := by simp

/-- The key algebraic identity: `eulerProd` has an exact “quadratic + z^4 remainder” form. -/
theorem eulerProd_eq_one_sub_z2_mul_sum_add_z4_mul (N : ℕ) (z : ℂ) :
    eulerProd z N = 1 - z ^ 2 * eulerSum N + z ^ 4 * eulerRemainder N z := by
  classical
  induction N with
  | zero =>
      simp [eulerProd, eulerSum, eulerRemainder]
  | succ N ih =>
      let c : ℂ := (1 : ℂ) / ((N : ℂ) + 1) ^ 2
      have hsum : eulerSum (N + 1) = eulerSum N + c := by
        simpa [c] using eulerSum_succ N
      have hrem :
          eulerRemainder (N + 1) z =
            eulerRemainder N z + eulerSum N * c - z ^ 2 * eulerRemainder N z * c := by
        simp [eulerRemainder, c]
      have hf : eulerFactor z N = 1 - z ^ 2 * c := by
        simp [eulerFactor, c, div_eq_mul_inv]
      calc
        eulerProd z (N + 1)
            = eulerProd z N * eulerFactor z N := eulerProd_succ z N
        _   = (1 - z ^ 2 * eulerSum N + z ^ 4 * eulerRemainder N z) * (1 - z ^ 2 * c) := by
              simp [ih, hf]
        _   = 1 - z ^ 2 * (eulerSum N + c)
                + z ^ 4 * (eulerRemainder N z + eulerSum N * c - z ^ 2 * eulerRemainder N z * c) := by
              ring_nf
        _   = 1 - z ^ 2 * eulerSum (N + 1) + z ^ 4 * eulerRemainder (N + 1) z := by
              simp [hsum, hrem, sub_eq_add_neg, add_assoc, mul_assoc]

/-- Continuity of `eulerRemainder N` (as a function `ℂ → ℂ`). -/
theorem continuous_eulerRemainder (N : ℕ) : Continuous (eulerRemainder N) := by
  induction N with
  | zero =>
      simpa [eulerRemainder] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℂ)))
  | succ N ih =>
      simpa [eulerRemainder] using by
        continuity

/--
Finite quadratic expansion as a little-o statement:

`eulerProd z N - (1 - z^2 * eulerSum N) = o(z^2)` as `z → 0`.
-/
theorem eulerProd_sub_quadratic_isLittleO (N : ℕ) :
    (fun z : ℂ => eulerProd z N - (1 - z ^ 2 * eulerSum N))
      =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
  -- side condition required by `isLittleO_iff_tendsto` in this snapshot
  have hzero :
      ∀ z : ℂ, (z ^ 2 = 0) →
        (eulerProd z N - (1 - z ^ 2 * eulerSum N)) = 0 := by
    intro z hz2
    have hz0 : z = 0 := by
      by_contra hz0
      exact (pow_ne_zero 2 hz0) hz2
    subst hz0
    simp [eulerProd, eulerFactor, eulerSum]

  -- exact representation as z^4 times the remainder
  have hrepr :
      ∀ z : ℂ, eulerProd z N - (1 - z ^ 2 * eulerSum N) = z ^ 4 * eulerRemainder N z := by
    intro z
    have h := eulerProd_eq_one_sub_z2_mul_sum_add_z4_mul (N := N) (z := z)
    rw [h]
    ring_nf

  -- show the quotient tends to 0
  have htend :
      Tendsto
        (fun z : ℂ => (eulerProd z N - (1 - z ^ 2 * eulerSum N)) / (z ^ 2))
        (𝓝 (0 : ℂ))
        (𝓝 (0 : ℂ)) := by
    -- rewrite the quotient as z^2 * R_N(z)
    have hquot :
        (fun z : ℂ => (eulerProd z N - (1 - z ^ 2 * eulerSum N)) / (z ^ 2))
          =
        (fun z : ℂ => z ^ 2 * eulerRemainder N z) := by
      funext z
      by_cases hz0 : z = 0
      · subst hz0
        simp [div_eq_mul_inv]
      ·
        have hz2 : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hz0
        have hpow : (z ^ 4) * (z ^ 2)⁻¹ = z ^ 2 :=
          pow_four_mul_inv_pow_two (z := z) hz2

        calc
          (eulerProd z N - (1 - z ^ 2 * eulerSum N)) / (z ^ 2)
              = (z ^ 4 * eulerRemainder N z) / (z ^ 2) := by
                  simp [hrepr]
          _   = (z ^ 4 * eulerRemainder N z) * (z ^ 2)⁻¹ := by
                  simp [div_eq_mul_inv]
          _   = ((z ^ 4) * (z ^ 2)⁻¹) * eulerRemainder N z := by
                  simp [mul_left_comm, mul_comm]
          _   = z ^ 2 * eulerRemainder N z := by
                  simp [hpow]

    have hR :
        Tendsto (eulerRemainder N) (𝓝 (0 : ℂ)) (𝓝 (eulerRemainder N 0)) :=
      (continuous_eulerRemainder N).tendsto 0

    have hz2t : Tendsto (fun z : ℂ => z ^ 2) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using
        (tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ))).pow 2

    have hmul :
        Tendsto (fun z : ℂ => z ^ 2 * eulerRemainder N z)
          (𝓝 (0 : ℂ))
          (𝓝 ((0 : ℂ) * eulerRemainder N 0)) :=
      hz2t.mul hR

    simpa [hquot] using (by simpa using hmul)

  -- package via the quotient characterization
  have hiff :=
    Asymptotics.isLittleO_iff_tendsto
      (f := fun z : ℂ => eulerProd z N - (1 - z ^ 2 * eulerSum N))
      (g := fun z : ℂ => z ^ 2)
      (l := 𝓝 (0 : ℂ)) hzero

  exact hiff.2 htend

end

end EulerBasel







