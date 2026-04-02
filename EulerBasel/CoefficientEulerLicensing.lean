/-
EulerBasel/CoefficientEulerLicensing.lean

Euler-faithful licensing layer (Step 1):

We set up a small open punctured neighborhood around 0 that lies inside
`Complex.integerComplement`, and we restrict the locally-uniform convergence
of the Euler partial products to this set.

This is the gateway needed later for `Complex.logDeriv_tendsto`.
-/

import EulerBasel.EulerProductExpansion
import EulerBasel.Coefficient  -- for `differentiableAt_finset_prod`
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

noncomputable section
open Classical
open scoped Topology BigOperators
open Filter

namespace EulerBasel

-- π as a complex number (local convenience).
local notation "piC" => ((Real.pi : ℝ) : ℂ)

/-- The raw Mathlib partial product (in the `1 + _root_.sineTerm` presentation). -/
def eulerPartialProd (N : ℕ) (z : ℂ) : ℂ :=
  ∏ n ∈ Finset.range N, (1 + _root_.sineTerm z n)

/-- The Mathlib limit function for the Euler sine product. -/
def eulerLimitFun (z : ℂ) : ℂ :=
  Complex.sin (Real.pi * z) / (Real.pi * z)

/-- Locally-uniform convergence of `eulerPartialProd` to `eulerLimitFun` on `integerComplement`. -/
theorem tendstoLocallyUniformlyOn_eulerPartialProd :
    TendstoLocallyUniformlyOn (fun N z => eulerPartialProd N z) eulerLimitFun atTop
      Complex.integerComplement := by
  simpa [eulerPartialProd, eulerLimitFun] using
    (HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange)

/-!
## Bridge: our `eulerProd` is the same finite product as Mathlib's `eulerPartialProd`.
-/

/-- `eulerFactor` matches `1 + _root_.sineTerm` termwise. -/
lemma eulerFactor_eq_one_add_root_sineTerm (z : ℂ) (n : ℕ) :
    eulerFactor z n = 1 + _root_.sineTerm z n := by
  -- In Mathlib, `_root_.sineTerm z n` simplifies to `-z^2 / ((n:ℂ)+1)^2`.
  -- We add `neg_div` to normalize `-(z^2 / a)` into `-z^2 / a`.
  simp [eulerFactor, _root_.sineTerm, sub_eq_add_neg, neg_div]

/-- Rewrite our `eulerProd` into the `∏ (1 + _root_.sineTerm)` product used by Mathlib. -/
lemma eulerProd_eq_prod_one_add_sineTerm (z : ℂ) (N : ℕ) :
    eulerProd z N = ∏ n ∈ Finset.range N, (1 + _root_.sineTerm z n) := by
  classical
  simp [eulerProd, eulerFactor_eq_one_add_root_sineTerm]

/-- Locally-uniform convergence of our `eulerProd` to `eulerLimitFun` on `integerComplement`. -/
theorem tendstoLocallyUniformlyOn_eulerProd :
    TendstoLocallyUniformlyOn (fun N z => eulerProd z N) eulerLimitFun atTop
      Complex.integerComplement := by
  simpa [eulerProd_eq_prod_one_add_sineTerm, eulerPartialProd] using
    (tendstoLocallyUniformlyOn_eulerPartialProd)

/-!
## Step 1: Choose a small open punctured neighborhood inside `integerComplement`.

We cannot use a ball containing `0` as a subset of `integerComplement`, since `0` is an integer.
Instead we use a punctured ball: `ball(0, 1/2) \ {0}`.
-/

/-- The punctured ball `|z| < 1/2` and `z ≠ 0`. -/
def nearZeroPunctured : Set ℂ :=
  Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) \ ({0} : Set ℂ)

/-- `nearZeroPunctured` is open. -/
lemma isOpen_nearZeroPunctured : IsOpen nearZeroPunctured := by
  have hopen :
      IsOpen (Metric.ball (0 : ℂ) ((1 / 2 : ℝ)) ∩ ({0} : Set ℂ)ᶜ) := by
    exact IsOpen.inter Metric.isOpen_ball isOpen_compl_singleton
  simpa [nearZeroPunctured, Set.diff_eq] using hopen

/-- Membership in `nearZeroPunctured` is `‖z‖ < 1/2` and `z ≠ 0`. -/
lemma mem_nearZeroPunctured_iff {z : ℂ} :
    z ∈ nearZeroPunctured ↔ (‖z‖ < (1 / 2 : ℝ) ∧ z ≠ 0) := by
  constructor
  · intro hz
    rcases hz with ⟨hzBall, hzNot⟩
    have hzlt : ‖z‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hz0 : z ≠ 0 := by
      -- `hzNot : z ∉ {0}`
      simpa [Set.mem_singleton_iff] using hzNot
    exact ⟨hzlt, hz0⟩
  · rintro ⟨hzlt, hz0⟩
    refine ⟨?_, ?_⟩
    · -- `z ∈ Metric.ball 0 (1/2)`
      simpa [Metric.mem_ball, dist_eq_norm] using hzlt
    · -- `z ∉ {0}`
      simpa [Set.mem_singleton_iff] using hz0

/--
If `n : ℤ` is nonzero, then `‖(n : ℂ)‖ ≥ 1`.
-/
lemma one_le_norm_intCast_of_ne_zero (n : ℤ) (hn : n ≠ 0) :
    (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
  have hne0 : Int.natAbs n ≠ 0 := by
    intro h
    have : n = 0 := (Int.natAbs_eq_zero.mp h)
    exact hn this
  have hpos : 0 < Int.natAbs n := Nat.pos_of_ne_zero hne0
  have hnat : (1 : ℕ) ≤ Int.natAbs n := by
    simpa [Nat.succ_le_iff] using hpos
  have hreal : (1 : ℝ) ≤ (Int.natAbs n : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- `nearZeroPunctured` sits inside `Complex.integerComplement`. -/
lemma nearZeroPunctured_subset_integerComplement :
    nearZeroPunctured ⊆ Complex.integerComplement := by
  intro z hz
  rcases hz with ⟨hzball, hz0⟩
  change z ∉ Set.range (fun n : ℤ => (n : ℂ))
  intro hzrange
  rcases hzrange with ⟨n, rfl⟩
  have hn : n ≠ 0 := by
    intro h
    subst h
    exact hz0 (by simp)
  have hge : (1 : ℝ) ≤ ‖(n : ℂ)‖ := one_le_norm_intCast_of_ne_zero n hn
  have hlt_half : ‖(n : ℂ)‖ < (1 / 2 : ℝ) := by
    -- hzball is membership in the ball, turn it into a norm inequality
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hlt_one : ‖(n : ℂ)‖ < (1 : ℝ) := lt_trans hlt_half (by norm_num)
  exact (not_lt_of_ge hge) hlt_one

/-- Restrict locally-uniform convergence to `nearZeroPunctured`. -/
theorem tendstoLocallyUniformlyOn_eulerProd_nearZeroPunctured :
    TendstoLocallyUniformlyOn (fun N z => eulerProd z N) eulerLimitFun atTop
      nearZeroPunctured := by
  exact (tendstoLocallyUniformlyOn_eulerProd.mono nearZeroPunctured_subset_integerComplement)

/-!
## Step 1.5: Nonvanishing of the limit on `nearZeroPunctured`

We need `eulerLimitFun z ≠ 0` for `z ∈ nearZeroPunctured` in order to apply
`Complex.logDeriv_tendsto` later.
-/

/-- The limit function `sin(πz)/(πz)` is nonzero on `nearZeroPunctured`. -/
lemma eulerLimitFun_ne_zero_of_mem_nearZeroPunctured {z : ℂ}
    (hz : z ∈ nearZeroPunctured) : eulerLimitFun z ≠ 0 := by
  rcases hz with ⟨hzball, hz0⟩
  have hz_ne : z ≠ 0 := by
    intro h; subst h; exact hz0 (by simp)

  intro hzero
  have hfrac : Complex.sin (Real.pi * z) / (Real.pi * z) = 0 := by
    simpa [eulerLimitFun] using hzero

  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hden : (Real.pi * z : ℂ) ≠ 0 := by
    exact mul_ne_zero hpi hz_ne

  have hnum0 : Complex.sin (Real.pi * z) = 0 := by
    have hor : Complex.sin (Real.pi * z) = 0 ∨ (Real.pi * z : ℂ) = 0 :=
      (div_eq_zero_iff).1 hfrac
    rcases hor with h | h
    · exact h
    · exact (hden h).elim

  -- `sin θ = 0 ↔ ∃ k : ℤ, θ = k * π`
  rcases (Complex.sin_eq_zero_iff).1 hnum0 with ⟨k, hk⟩

  -- Cancel `π` to get `z = k`
  have hz_eq : z = (k : ℂ) := by
    have hk' : (Real.pi : ℂ) * z = (Real.pi : ℂ) * (k : ℂ) := by
      -- hk : (Real.pi:ℂ) * z = k * (Real.pi:ℂ)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hk
    exact (mul_left_cancel₀ hpi) hk'

  have hk0 : k ≠ 0 := by
    intro hk0
    have : z = 0 := by simpa [hk0] using hz_eq
    exact hz_ne this

  have hge : (1 : ℝ) ≤ ‖(k : ℂ)‖ := one_le_norm_intCast_of_ne_zero k hk0
  have hlt_half : ‖(k : ℂ)‖ < (1 / 2 : ℝ) := by
    -- hzball is membership in the ball, turn it into a norm inequality
    have hzlt : ‖z‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzball
    simpa [hz_eq] using hzlt
  have hlt_one : ‖(k : ℂ)‖ < (1 : ℝ) := lt_trans hlt_half (by norm_num)
  exact (not_lt_of_ge hge) hlt_one

/-!
## Step 1.6: A clean “eventually differentiable on” lemma

This is just plumbing for `Complex.logDeriv_tendsto`.
-/

private lemma differentiableOn_eulerProd (N : ℕ) (s : Set ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => eulerProd z N) s := by
  intro z hz
  -- Prove `DifferentiableAt` and downgrade to `DifferentiableWithinAt`.
  have hAt : DifferentiableAt ℂ (fun w : ℂ => eulerProd w N) z := by
    classical
    have hf : ∀ n ∈ Finset.range N, DifferentiableAt ℂ (fun w : ℂ => eulerFactor w n) z := by
      intro n hn
      have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z :=
        (differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).pow 2
      have hdiv :
          DifferentiableAt ℂ (fun w : ℂ => (w ^ 2) / ((n : ℂ) + 1) ^ 2) z :=
        hpow.div_const (((n : ℂ) + 1) ^ 2)
      dsimp [eulerFactor]
      have hconst : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) z := by
        exact (differentiableAt_const (𝕜 := ℂ) (c := (1 : ℂ)) (x := z))
      exact hconst.sub hdiv

    -- Use the helper from `EulerBasel.Coefficient`.
    simpa [eulerProd] using
      (differentiableAt_finset_prod (s := Finset.range N)
        (f := fun n : ℕ => fun w : ℂ => eulerFactor w n) (z := z) hf)
  exact hAt.differentiableWithinAt

theorem eventually_differentiableOn_eulerProd_nearZeroPunctured :
    (∀ᶠ N : ℕ in (atTop : Filter ℕ),
      DifferentiableOn ℂ (fun z : ℂ => eulerProd z N) nearZeroPunctured) := by
  refine Filter.Eventually.of_forall ?_
  intro N
  exact differentiableOn_eulerProd N nearZeroPunctured

end EulerBasel





