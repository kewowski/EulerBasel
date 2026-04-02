/-
EulerBasel/EulerRationalBounds.lean

Snapshot-stable p-series plumbing for the “pure Euler” Phase 2 bounds.

We use:
  Real.summable_one_div_nat_add_rpow
and convert it into summability of the complex Basel summand via `Summable.of_norm`.
-/

import EulerBasel.CoefficientDefs
import Mathlib.Analysis.PSeries

namespace EulerBasel

open scoped Topology BigOperators
open Filter

noncomputable section

/-- Helper: `(n:ℝ)+1` is nonnegative. -/
lemma nat_cast_add_one_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) + 1 := by
  nlinarith

/--
Compute `‖(n:ℂ)+1‖` as a real number, without `norm_cast` and without simp loops.
-/
lemma norm_nat_add_one_complex (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  have hnpos : 0 ≤ (n : ℝ) + 1 := nat_cast_add_one_nonneg n
  have hcast : (n : ℂ) + 1 = ((n : ℝ) + 1 : ℂ) := by simp
  calc
    ‖(n : ℂ) + 1‖
        = ‖((n : ℝ) + 1 : ℂ)‖ := by simp [hcast]
    _   = |(n : ℝ) + 1| := by simpa using (Complex.norm_real ((n : ℝ) + 1))
    _   = (n : ℝ) + 1 := by simp [abs_of_nonneg hnpos]

/--
Exact norm formula in Nat-power form.

Key point: we **do not** do `simp` and then `rw [norm_pow]`.
Instead, we do one controlled `simp` that includes `norm_pow`.
-/
lemma norm_baselTerm_natPow (n : ℕ) :
    ‖baselTerm n‖ = (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ) := by
  change ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (2 : ℕ)‖ = (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ)
  simp [norm_pow, norm_nat_add_one_complex n]

/--
Summability of the real comparison series in Nat-power form,
proved by converting the `rpow` p-series lemma.
-/
lemma summable_one_div_nat_add_one_sq_natPow :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
  have h_rpow_abs :
      Summable (fun n : ℕ => (1 : ℝ) / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
    -- In this snapshot, this lemma is an iff.
    exact (Real.summable_one_div_nat_add_rpow (a := (1 : ℝ)) (s := (2 : ℝ))).2 (by norm_num)

  -- Remove the absolute value using `(n:ℝ)+1 ≥ 0`, then convert `rpow` (2:ℝ) to `pow` (2:ℕ).
  refine h_rpow_abs.congr ?_
  intro n
  have hnpos : 0 ≤ (n : ℝ) + 1 := nat_cast_add_one_nonneg n
  -- `simp` handles: `abs_of_nonneg`, and `Real.rpow_natCast`/`rpow_two`-style rewriting in this snapshot.
  simp [abs_of_nonneg hnpos]

/-- The real norm series of the Basel term is summable. -/
lemma summable_norm_baselTerm : Summable (fun n : ℕ => ‖baselTerm n‖) := by
  refine (summable_one_div_nat_add_one_sq_natPow).congr ?_
  intro n
  exact (norm_baselTerm_natPow n).symm

/-- The complex Basel summand is summable. -/
lemma summable_baselTerm : Summable (fun n : ℕ => baselTerm n) := by
  exact Summable.of_norm summable_norm_baselTerm

end

end EulerBasel