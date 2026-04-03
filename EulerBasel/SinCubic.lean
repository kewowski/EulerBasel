/-
EulerBasel/SinCubic.lean

Series (Euler-faithful) route toward the cubic expansion of `Complex.sin` at 0,
organized for a dominated-convergence proof.

This file is intentionally *series-only*: no calculus detours.
-/

import Mathlib
import EulerBasel.Taylor
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic

open scoped Topology BigOperators
open Filter

namespace EulerBasel

/-- Tail representation used:
`sin z - z = ∑' n, if n=0 then 0 else sinTerm z n`. -/
noncomputable def sinTail1 (z : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else sinTerm z n

/-- Cubic coefficient supported only at `n = 1`. -/
noncomputable def cubicCoeff (n : ℕ) : ℂ :=
  if n = 1 then (-(1 / 6 : ℂ)) else 0

/-- Normalized remainder term (subtract cubic piece, then divide by `z^3`). -/
noncomputable def remTerm (z : ℂ) (n : ℕ) : ℂ :=
  (sinTail1 z n - cubicCoeff n * z ^ 3) / z ^ 3

/-- Dominating series (real-valued). -/
noncomputable def dom (n : ℕ) : ℝ :=
  ‖sinTerm (1 : ℂ) n‖

lemma dom_eq_inv_odd_factorial (n : ℕ) :
    dom n = 1 / ((((2 * n + 1).factorial : ℕ) : ℝ)) := by
  simp [dom, sinTerm]

lemma summable_dom : Summable dom := by
  have hmodel : Summable (fun n : ℕ => (1 : ℝ) ^ n / (n.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial (1 : ℝ)
  refine Summable.of_nonneg_of_le ?_ ?_ hmodel
  · intro n
    rw [dom_eq_inv_odd_factorial]
    positivity
  · intro n
    rw [dom_eq_inv_odd_factorial]
    have hfac : n.factorial ≤ (2 * n + 1).factorial := by
      apply Nat.factorial_le
      omega
    have hfacR : (n.factorial : ℝ) ≤ ((((2 * n + 1).factorial : ℕ) : ℝ)) := by
      exact_mod_cast hfac
    have hpos : (0 : ℝ) < (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have hinv :
        1 / ((((2 * n + 1).factorial : ℕ) : ℝ)) ≤ 1 / (n.factorial : ℝ) := by
      exact one_div_le_one_div_of_le hpos hfacR
    simpa using hinv

/-- `z ≠ 0` eventually in the punctured neighbourhood. -/
private lemma eventually_ne_zero_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := by
  change {z : ℂ | z ≠ 0} ∈ nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  rw [nhdsWithin, Filter.mem_inf_iff]
  refine ⟨Set.univ, Filter.univ_mem, {z : ℂ | z ≠ 0}, mem_principal_self _, ?_⟩
  simp

/-- Eventually `‖z‖ ≤ 1` in the punctured neighbourhood of 0. -/
lemma eventually_norm_le_one_punctured :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ ≤ 1 := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := by
    simpa using Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
  have hball' : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
    mem_nhdsWithin_of_mem_nhds hball
  filter_upwards [hball'] with z hz
  have : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  exact le_of_lt this

/-- If `0 ≤ r ≤ 1` then `r^k ≤ 1`. -/
lemma pow_le_one_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ k : ℕ, r ^ k ≤ (1 : ℝ)
  | 0 => by simp
  | Nat.succ k =>
      have ih : r ^ k ≤ (1 : ℝ) := pow_le_one_of_le_one hr0 hr1 k
      calc
        r ^ (Nat.succ k) = r ^ k * r := by simp [pow_succ]
        _ ≤ (1 : ℝ) * r := by gcongr
        _ ≤ (1 : ℝ) * (1 : ℝ) := by gcongr
        _ = (1 : ℝ) := by ring

/-- `‖z‖ → 0` on the punctured neighbourhood of 0. -/
lemma tendsto_norm_punctured :
    Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
  have h :
      Tendsto (fun z : ℂ => ‖z‖) (𝓝 (0 : ℂ)) (𝓝 (‖(0 : ℂ)‖ : ℝ)) := by
    simpa using
      ((continuous_norm : Continuous (fun z : ℂ => ‖z‖)).continuousAt (x := (0 : ℂ))).tendsto
  have h' : Tendsto (fun z : ℂ => ‖z‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa [norm_zero] using h
  exact h'.mono_left nhdsWithin_le_nhds

/-- `z^m → 0` on the punctured neighbourhood. -/
lemma tendsto_pow_punctured (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun z : ℂ => z ^ m) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  have hnorm_pow : Tendsto (fun z : ℂ => ‖z ^ m‖) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    have hpowR :
        Tendsto (fun z : ℂ => (‖z‖ : ℝ) ^ m) (𝓝[≠] (0 : ℂ)) (𝓝 ((0 : ℝ) ^ m)) := by
      simpa using (tendsto_norm_punctured.pow m)
    have : ((0 : ℝ) ^ m) = 0 := by
      simp [zero_pow, hm]
    have hpowR' :
        Tendsto (fun z : ℂ => ‖z‖ ^ m) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
      simpa [this] using hpowR
    simpa [norm_pow] using hpowR'
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_pow

/-- Convert `‖f z‖ → 0` into `f z → 0`. -/
lemma tendsto_zero_of_norm_tendsto_zero {α : Type} {l : Filter α} {f : α → ℂ} :
    Tendsto (fun x => ‖f x‖) l (𝓝 (0 : ℝ)) → Tendsto f l (𝓝 (0 : ℂ)) := by
  intro h
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  have h' := h ε hε
  simpa [dist_eq_norm] using h'

/-- Pointwise limit: `remTerm z n → 0` on the punctured neighbourhood. -/
lemma tendsto_remTerm (n : ℕ) :
    Tendsto (fun z : ℂ => remTerm z n) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  cases n with
  | zero =>
      simp [remTerm, sinTail1, cubicCoeff]
  | succ n =>
      cases n with
      | zero =>
          simp [remTerm, sinTail1, cubicCoeff, sinTerm_one]
      | succ n =>
          have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_ne_zero_punctured
          let c : ℂ := sinTerm (1 : ℂ) (Nat.succ (Nat.succ n))
          have hm : (2 * n + 2 : ℕ) ≠ 0 := Nat.succ_ne_zero _
          have hpow :
              Tendsto (fun z : ℂ => z ^ (2 * n + 2)) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
            tendsto_pow_punctured (m := 2 * n + 2) hm

          have hnormpow :
              Tendsto (fun z : ℂ => ‖z ^ (2 * n + 2)‖) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
            have :
                Tendsto (fun z : ℂ => ‖z ^ (2 * n + 2)‖) (𝓝[≠] (0 : ℂ))
                  (𝓝 (‖(0 : ℂ)‖ : ℝ)) :=
              (((continuous_norm : Continuous (fun w : ℂ => ‖w‖)).continuousAt (x := (0 : ℂ))).tendsto.comp
                hpow)
            simpa [norm_zero] using this

          have hnorm :
              Tendsto (fun z : ℂ => ‖c * z ^ (2 * n + 2)‖) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
            have ht :
                Tendsto (fun z : ℂ => (‖c‖ : ℝ) * ‖z ^ (2 * n + 2)‖)
                  (𝓝[≠] (0 : ℂ)) (𝓝 ((‖c‖ : ℝ) * 0)) := by
              simpa using (tendsto_const_nhds.mul hnormpow)
            have ht' :
                Tendsto (fun z : ℂ => (‖c‖ : ℝ) * ‖z ^ (2 * n + 2)‖)
                  (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
              simpa [mul_zero] using ht
            simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using ht'

          have hmul :
              Tendsto (fun z : ℂ => c * z ^ (2 * n + 2)) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
            tendsto_zero_of_norm_tendsto_zero hnorm

          refine (tendsto_congr' ?_).1 hmul
          filter_upwards [hne] with z hz0

          have hc0 : cubicCoeff (Nat.succ (Nat.succ n)) = 0 := by
            simp [cubicCoeff]
          have ht : sinTail1 z (Nat.succ (Nat.succ n)) = sinTerm z (Nat.succ (Nat.succ n)) := by
            simp [sinTail1]

          have hfac :
              sinTerm z (Nat.succ (Nat.succ n)) =
                sinTerm (1 : ℂ) (Nat.succ (Nat.succ n)) * z ^ 5 * z ^ (n * 2) := by
            simp [sinTerm]
            ring_nf

          simp [remTerm, ht, hc0, sub_zero, div_eq_mul_inv, c, hfac]
          field_simp [hz0]
          ring_nf

/-- Domination for dominated convergence. -/
lemma dominated_bound :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ∀ n : ℕ, ‖remTerm z n‖ ≤ dom n := by
  have hle : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ ≤ 1 := eventually_norm_le_one_punctured
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_ne_zero_punctured
  filter_upwards [hle, hne] with z hzle hz0 n
  cases n with
  | zero =>
      simp [remTerm, sinTail1, cubicCoeff, dom]
  | succ n =>
      cases n with
      | zero =>
          simp [remTerm, sinTail1, cubicCoeff, sinTerm_one, dom]
      | succ n =>
          have hc0 : cubicCoeff (Nat.succ (Nat.succ n)) = 0 := by
            simp [cubicCoeff]
          have ht : sinTail1 z (Nat.succ (Nat.succ n)) = sinTerm z (Nat.succ (Nat.succ n)) := by
            simp [sinTail1]
          let c : ℂ := sinTerm (1 : ℂ) (Nat.succ (Nat.succ n))
          have hfac :
              sinTerm z (Nat.succ (Nat.succ n)) =
                sinTerm (1 : ℂ) (Nat.succ (Nat.succ n)) * z ^ 5 * z ^ (n * 2) := by
            simp [sinTerm]
            ring_nf
          have hrepr :
              remTerm z (Nat.succ (Nat.succ n)) = c * z ^ (2 * n + 2) := by
            simp [remTerm, ht, hc0, sub_zero, div_eq_mul_inv, c, hfac]
            field_simp [hz0]
            ring_nf
          have hzpow : ‖z‖ ^ (2 * n + 2) ≤ (1 : ℝ) :=
            pow_le_one_of_le_one (norm_nonneg z) hzle (2 * n + 2)
          calc
            ‖remTerm z (Nat.succ (Nat.succ n))‖ = ‖c * z ^ (2 * n + 2)‖ := by
              simp [hrepr]
            _ = ‖c‖ * ‖z ^ (2 * n + 2)‖ := by
              simp
            _ = ‖c‖ * (‖z‖ ^ (2 * n + 2)) := by
              simp [norm_pow]
            _ ≤ ‖c‖ * 1 := by
              gcongr
            _ = dom (Nat.succ (Nat.succ n)) := by
              simp [dom, c]

/-- Dominated convergence on the normalized remainder series. -/
theorem tendsto_tsum_remTerm :
    Tendsto (fun z : ℂ => ∑' n : ℕ, remTerm z n) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  have hsum : Summable dom := summable_dom
  have hab : ∀ n : ℕ, Tendsto (fun z => remTerm z n) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    tendsto_remTerm
  have hbound :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ∀ n : ℕ, ‖remTerm z n‖ ≤ dom n :=
    dominated_bound
  simpa using
    (tendsto_tsum_of_dominated_convergence
      (f := remTerm) (g := fun _ : ℕ => (0 : ℂ)) (bound := dom)
      hsum hab hbound)

/-!
## Final target forms
-/

/-- Remainder form: tends to 0. -/
theorem tendsto_sin_sub_id_add_cubic_div_cubic :
    Tendsto
      (fun z : ℂ => (Complex.sin z - z - (-(1 / 6 : ℂ) * z ^ 3)) / z ^ 3)
      (𝓝[≠] (0 : ℂ))
      (𝓝 0) := by
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_ne_zero_punctured
  refine (tendsto_congr' ?_).1 tendsto_tsum_remTerm
  filter_upwards [hne] with z hz0
  have hz3 : (z ^ 3 : ℂ) ≠ 0 := pow_ne_zero 3 hz0

  have hs_sinTerm : HasSum (sinTerm z) (Complex.sin z) := hasSum_sinTerm z
  let g0 : ℕ → ℂ := fun n => if n = 0 then sinTerm z 0 else 0
  have hs_g0 : HasSum g0 (sinTerm z 0) := by
    simpa [g0, eq_comm] using
      (hasSum_ite_eq (α := ℂ) (β := ℕ) (b := 0) (a := sinTerm z 0))
  have hs_tail' :
      HasSum (fun n => sinTerm z n - g0 n) (Complex.sin z - sinTerm z 0) :=
    hs_sinTerm.sub hs_g0

  have hs_tail : HasSum (sinTail1 z) (Complex.sin z - z) := by
    have hcongr : ∀ n : ℕ, sinTail1 z n = (sinTerm z n - g0 n) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp [sinTail1, g0]
      · simp [sinTail1, g0, hn]
    have hs1 : HasSum (sinTail1 z) (Complex.sin z - sinTerm z 0) :=
      HasSum.congr_fun hs_tail' hcongr
    simpa [sinTerm] using hs1

  let f : ℕ → ℂ := fun n => (sinTail1 z n) / z ^ 3
  let δ : ℕ → ℂ := fun n => if n = 1 then (6⁻¹ : ℂ) else 0

  have hs_f : HasSum f ((Complex.sin z - z) / z ^ 3) := by
    have h := hs_tail.mul_right ((z ^ 3)⁻¹)
    simpa [f, div_eq_mul_inv, mul_assoc] using h

  have hs_δ : HasSum δ (6⁻¹ : ℂ) := by
    simpa [δ, eq_comm] using
      (hasSum_ite_eq (α := ℂ) (β := ℕ) (b := 1) (a := (6⁻¹ : ℂ)))

  have hsplit : (fun n => remTerm z n) = fun n => f n + δ n := by
    funext n
    by_cases hn : n = 1
    · subst hn
      have hc1 : cubicCoeff 1 = (-(1 / 6 : ℂ)) := by
        simp [cubicCoeff]
      have hlin' :
          (sinTail1 z 1 + (6⁻¹ : ℂ) * z ^ 3) / z ^ 3
            = (sinTail1 z 1) / z ^ 3 + (6⁻¹ : ℂ) := by
        have hz3' : (z ^ 3 : ℂ) ≠ 0 := hz3
        simp [div_eq_mul_inv, hz3', add_mul]
      simp [remTerm, f, δ, hc1, hlin']
    · have hc0 : cubicCoeff n = 0 := by
        simp [cubicCoeff, hn]
      simp [remTerm, f, δ, hn, hc0]

  have hs_rem :
      HasSum (fun n => remTerm z n) (((Complex.sin z - z) / z ^ 3) + (6⁻¹ : ℂ)) := by
    have hs_sum :
        HasSum (fun n => f n + δ n) (((Complex.sin z - z) / z ^ 3) + (6⁻¹ : ℂ)) :=
      hs_f.add hs_δ
    simpa [hsplit] using hs_sum

  have htsum :
      (∑' n : ℕ, remTerm z n) = ((Complex.sin z - z) / z ^ 3) + (6⁻¹ : ℂ) := by
    exact hs_rem.tsum_eq

  calc
    (∑' n : ℕ, remTerm z n)
        = ((Complex.sin z - z) / z ^ 3) + (6⁻¹ : ℂ) := htsum
    _ = ((Complex.sin z - z) + (6⁻¹ : ℂ) * z ^ 3) / z ^ 3 := by
      field_simp [hz3]
    _ = (Complex.sin z - z - (-(1 / 6 : ℂ) * z ^ 3)) / z ^ 3 := by
      ring

/-- Main cubic expansion form. -/
theorem tendsto_sin_sub_id_div_cubic :
    Tendsto
      (fun z : ℂ => (Complex.sin z - z) / z ^ 3)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-(1 / 6 : ℂ))) := by
  have hrem := tendsto_sin_sub_id_add_cubic_div_cubic
  have hconst :
      Tendsto (fun _ : ℂ => (6⁻¹ : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (6⁻¹ : ℂ)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun z : ℂ =>
          ((Complex.sin z - z - (-(1 / 6 : ℂ) * z ^ 3)) / z ^ 3) - (6⁻¹ : ℂ))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (0 - (6⁻¹ : ℂ))) := by
    exact hrem.sub hconst
  refine (tendsto_congr' ?_).2 (by simpa using hsub)
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_ne_zero_punctured
  filter_upwards [hne] with z hz0
  have hz3 : (z ^ 3 : ℂ) ≠ 0 := pow_ne_zero 3 hz0
  field_simp [hz3]
  ring_nf

end EulerBasel