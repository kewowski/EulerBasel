/-
EulerBasel/QuadraticCoefficient.lean

Uniqueness of the quadratic coefficient via little-o.

If a function has two quadratic expansions with little-o(z^2) remainder at 0,
then the quadratic coefficients agree.

We avoid any “eventually z ≠ 0” reasoning at `𝓝 0` by composing with a concrete
nonzero real sequence `r_n → 0` and viewing it in `ℂ` via `Complex.ofReal`.
-/

import EulerBasel.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

open scoped Topology BigOperators Asymptotics
open Filter

namespace EulerBasel

noncomputable section

/-- A small nonzero real sequence tending to 0: `r_n = 1/((n:ℝ)+1)`. -/
def rSeq (n : ℕ) : ℝ := (1 : ℝ) / ((n : ℝ) + 1)

/-- The same sequence viewed in `ℂ`. -/
def zSeq (n : ℕ) : ℂ := Complex.ofReal (rSeq n)

lemma rSeq_ne_zero (n : ℕ) : rSeq n ≠ 0 := by
  have hden : ((n : ℝ) + 1) ≠ 0 := by
    have : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
    exact_mod_cast this
  simp [rSeq, hden]

lemma zSeq_ne_zero (n : ℕ) : zSeq n ≠ 0 := by
  have hn : rSeq n ≠ 0 := rSeq_ne_zero n
  intro hz
  have : rSeq n = 0 := (Complex.ofReal_eq_zero.mp hz)
  exact hn this

/-- `((n:ℝ)+1) → ∞` as `n → ∞` (in the `atTop` filter). -/
lemma tendsto_natCast_add_one_atTop :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  refine (eventually_atTop.2 ?_)
  refine ⟨Nat.ceil b, ?_⟩
  intro n hn
  have hbceil : b ≤ (Nat.ceil b : ℝ) := by
    simpa using (Nat.le_ceil b)
  have hceil_le : (Nat.ceil b : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hb_le_n : b ≤ (n : ℝ) := le_trans hbceil hceil_le
  have hn_le : (n : ℝ) ≤ (n : ℝ) + 1 := by
    exact le_add_of_nonneg_right (by norm_num)
  exact le_trans hb_le_n hn_le

lemma tendsto_rSeq : Tendsto rSeq atTop (𝓝 (0 : ℝ)) := by
  have hinv :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_add_one_atTop)
  -- Avoid fragile `simp` here: rewrite pointwise by hand.
  -- `rSeq n = ((n:ℝ)+1)⁻¹`.
  have hrew : (fun n : ℕ => rSeq n) = fun n : ℕ => (((n : ℝ) + 1)⁻¹) := by
    funext n
    simp [rSeq, div_eq_mul_inv]
  simpa [hrew] using hinv

lemma tendsto_zSeq : Tendsto zSeq atTop (𝓝 (0 : ℂ)) := by
  -- map the real limit through `Complex.ofReal`, then rewrite.
  have hmap :
      Tendsto (fun n : ℕ => Complex.ofReal (rSeq n)) atTop (𝓝 (Complex.ofReal 0)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_rSeq
  simpa [zSeq] using hmap

/--
If `f z = 1 - a z^2 + o(z^2)` and also `f z = 1 - b z^2 + o(z^2)` as `z → 0`,
then `a = b`.
-/
theorem quadratic_coeff_unique
    (f : ℂ → ℂ) (a b : ℂ)
    (ha : (fun z : ℂ => f z - (1 - a * z ^ 2)) =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2))
    (hb : (fun z : ℂ => f z - (1 - b * z ^ 2)) =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2)) :
    a = b := by
  -- difference of the two little-o remainders
  have hdiff0 :
      (fun z : ℂ =>
        (f z - (1 - a * z ^ 2)) - (f z - (1 - b * z ^ 2)))
        =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) :=
    ha.sub hb

  -- `ha.sub hb` simplifies to `a*z^2 - b*z^2`.
  -- Convert it to `(a-b)*z^2` via explicit pointwise identities.
  have hEq' :
      (fun z : ℂ =>
        (f z - (1 - a * z ^ 2)) - (f z - (1 - b * z ^ 2)))
        =
      (fun z : ℂ => a * z ^ 2 - b * z ^ 2) := by
    funext z
    ring

  have hEq'' :
      (fun z : ℂ => a * z ^ 2 - b * z ^ 2)
        =
      (fun z : ℂ => (a - b) * z ^ 2) := by
    funext z
    ring

  have hdiff :
      (fun z : ℂ => (a - b) * z ^ 2) =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
    have h1 :
        (fun z : ℂ => a * z ^ 2 - b * z ^ 2) =o[𝓝 (0 : ℂ)] (fun z : ℂ => z ^ 2) := by
      simpa [hEq'] using hdiff0
    simpa [hEq''] using h1

  -- quotient characterisation
  have hzero :
      ∀ z : ℂ, (z ^ 2 = 0) → ((a - b) * z ^ 2) = 0 := by
    intro z hz2
    simp [hz2]

  have hiff :=
    Asymptotics.isLittleO_iff_tendsto
      (f := fun z : ℂ => (a - b) * z ^ 2)
      (g := fun z : ℂ => z ^ 2)
      (l := 𝓝 (0 : ℂ)) hzero

  have htend :
      Tendsto (fun z : ℂ => ((a - b) * z ^ 2) / (z ^ 2))
        (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    (hiff.1 hdiff)

  -- compose with the explicit nonzero sequence `zSeq n → 0`
  have htend_seq :
      Tendsto (fun n : ℕ => ((a - b) * (zSeq n) ^ 2) / ((zSeq n) ^ 2))
        atTop (𝓝 (0 : ℂ)) :=
    htend.comp tendsto_zSeq

  -- compute the quotient termwise: it is constantly `a - b`
  have hconst :
      (fun n : ℕ => ((a - b) * (zSeq n) ^ 2) / ((zSeq n) ^ 2)) = fun _ : ℕ => (a - b) := by
    funext n
    have hnz : (zSeq n : ℂ) ≠ 0 := zSeq_ne_zero n
    have hnz2 : ((zSeq n) ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hnz
    -- `simp` closes this in your project elsewhere; keep it simple.
    simp [div_eq_mul_inv, hnz2]

  have h_to0 : Tendsto (fun _ : ℕ => (a - b)) atTop (𝓝 (0 : ℂ)) := by
    simpa [hconst] using htend_seq

  -- constant also tends to itself
  have h_toab : Tendsto (fun _ : ℕ => (a - b)) atTop (𝓝 (a - b)) :=
    tendsto_const_nhds

  have hab : a - b = 0 := by
    -- uniqueness of limits in Hausdorff spaces
    exact tendsto_nhds_unique h_toab h_to0

  exact sub_eq_zero.mp hab

end
end EulerBasel