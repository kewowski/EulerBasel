import EulerBasel.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

noncomputable section
open Classical
open scoped Topology
open Filter

namespace EulerBasel

/-!
Taylor.lean

# Series-side toolbox for `sin`

This file is intentionally self-contained.

It defines the termwise series `sinTerm`, records `HasSum (sinTerm z) (sin z)`,
and provides a clean tail identity for `sin z - z` as a `tsum` with an `if`-mask.

-/

/-- The `n`th term in the power series for `Complex.sin`. Matches `Complex.hasSum_sin` exactly. -/
noncomputable def sinTerm (z : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * z ^ (2 * n + 1) / (↑(2 * n + 1).factorial : ℂ)

lemma hasSum_sinTerm (z : ℂ) :
    HasSum (sinTerm z) (Complex.sin z) := by
  simpa [sinTerm] using (Complex.hasSum_sin z)

lemma sinTerm_zero (z : ℂ) : sinTerm z 0 = z := by
  simp [sinTerm]

lemma sinTerm_one (z : ℂ) : sinTerm z 1 = - (1 / 6 : ℂ) * z ^ 3 := by
  have hfact : (↑(Nat.factorial 3) : ℂ) = (6 : ℂ) := by
    norm_num
  simp [sinTerm, hfact, div_eq_mul_inv]
  ring

/-- A convenient tail identity: `sin z - z` is the `tsum` of the masked series with the `n=0` term removed. -/
lemma sin_sub_id_eq_tsum_tail (z : ℂ) :
    Complex.sin z - z = ∑' n : ℕ, (if n = 0 then (0 : ℂ) else sinTerm z n) := by
  -- Start from `sin = tsum`, then rewrite by separating the `n=0` term.
  have hsin : Complex.sin z = ∑' n : ℕ, sinTerm z n := by
    -- `HasSum` gives `tsum (sinTerm z) = sin z`; we want the symmetric form.
    simpa using (hasSum_sinTerm z).tsum_eq.symm

  -- In this snapshot, the following lemma exists:
  --   `Summable.tsum_eq_add_tsum_ite'` (method-form split lemma)
  have hs : Summable (sinTerm z) := (hasSum_sinTerm z).summable
  have hs_upd : Summable (Function.update (sinTerm z) 0 0) :=
    hs.update 0 (0 : ℂ)

  have hsplit :
      (∑' n : ℕ, sinTerm z n)
        = sinTerm z 0 + ∑' n : ℕ, (if n = 0 then (0 : ℂ) else sinTerm z n) := by
    -- Use the split lemma at `b = 0`.
    simpa [Function.update] using
      (Summable.tsum_eq_add_tsum_ite' (L := SummationFilter.unconditional ℕ)
        (α := ℂ) (β := ℕ) (f := sinTerm z) (b := 0) hs_upd)

  -- Now cancel the head term `sinTerm z 0 = z`.
  calc
    Complex.sin z - z
        = (∑' n : ℕ, sinTerm z n) - z := by
            simp [hsin]
    _   = (sinTerm z 0 + ∑' n : ℕ, (if n = 0 then (0 : ℂ) else sinTerm z n)) - z := by
            simp [hsplit]
    _   = ∑' n : ℕ, (if n = 0 then (0 : ℂ) else sinTerm z n) := by
            simp [sinTerm_zero, sub_eq_add_neg, add_assoc]

end EulerBasel
