/-
EulerBasel/Coefficient.lean

Coefficient extraction via logarithmic derivative (Euler-style licensing layer).

Defines `logDerivC f z = deriv f z / f z` and proves the finite-product identity

  logDerivC (∏ i∈s, f i) z = ∑ i∈s, logDerivC (f i) z

under termwise differentiability and non-vanishing hypotheses at `z`.

This avoids snapshot-dependent `logDeriv` APIs.
-/

import EulerBasel.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic  -- `field_simp`

noncomputable section
open Classical
open scoped BigOperators

namespace EulerBasel

-- π as a complex number (local convenience).
local notation "piC" => ((Real.pi : ℝ) : ℂ)

/-- Logarithmic derivative, defined directly (stable across snapshots). -/
def logDerivC (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv f z / f z

/-- Differentiability of a finite product from termwise differentiability. -/
lemma differentiableAt_finset_prod
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _
    simp
  · intro a s ha ih hf
    have hf_a : DifferentiableAt ℂ (f a) z := hf a (by simp [ha])
    have hf_s : ∀ i ∈ s, DifferentiableAt ℂ (f i) z := by
      intro i hi
      exact hf i (by simp [hi])
    have ih_s : DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z := ih hf_s
    have hmul : DifferentiableAt ℂ (fun w => f a w * (∏ i ∈ s, f i w)) z :=
      hf_a.mul ih_s
    have hprod :
        (fun w => ∏ i ∈ insert a s, f i w)
          = (fun w => f a w * (∏ i ∈ s, f i w)) := by
      funext w
      exact (Finset.prod_insert (s := s) (a := a) (f := fun i => f i w) ha)
    -- transport differentiability along definitional equality
    rw [hprod]
    exact hmul

/-- Log-derivative of a product, assuming differentiability and non-vanishing at the point. -/
lemma logDerivC_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hf0 : f z ≠ 0) (hg0 : g z ≠ 0) :
    logDerivC (fun w => f w * g w) z = logDerivC f z + logDerivC g z := by
  have hderiv :
      deriv (fun w => f w * g w) z = deriv f z * g z + f z * deriv g z :=
    (hf.hasDerivAt.mul hg.hasDerivAt).deriv
  unfold logDerivC
  rw [hderiv]
  -- Clear denominators; this snapshot’s `field_simp` finishes the algebra.
  field_simp [hf0, hg0]

/--
Finite-product version of Euler’s “log derivative turns product into sum”.

For a finite set `s`, if each factor `f i` is differentiable at `z` and nonzero at `z`, then:

`logDerivC (∏ i∈s, f i) z = ∑ i∈s, logDerivC (f i) z`.
-/
lemma logDerivC_finset_prod
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) z)
    (h0 : ∀ i ∈ s, f i z ≠ 0) :
    logDerivC (fun w => ∏ i ∈ s, f i w) z
      = ∑ i ∈ s, logDerivC (f i) z := by
  classical
  revert hf h0
  refine Finset.induction_on s ?base ?step
  · intro _ _
    simp [logDerivC]
  · intro a s ha ih hf h0
    have hf_a : DifferentiableAt ℂ (f a) z := hf a (by simp [ha])
    have h0_a : f a z ≠ 0 := h0 a (by simp [ha])

    have hf_s : ∀ i ∈ s, DifferentiableAt ℂ (f i) z := by
      intro i hi
      exact hf i (by simp [hi])
    have h0_s : ∀ i ∈ s, f i z ≠ 0 := by
      intro i hi
      exact h0 i (by simp [hi])

    have hf_prod : DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z :=
      differentiableAt_finset_prod (s := s) (f := f) (z := z) hf_s
    have h0_prod : (∏ i ∈ s, f i z) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 ?_
      intro i hi
      exact h0_s i hi

    have hmul :
        logDerivC (fun w => f a w * (∏ i ∈ s, f i w)) z
          = logDerivC (f a) z + logDerivC (fun w => ∏ i ∈ s, f i w) z :=
      logDerivC_mul (f := fun w => f a w) (g := fun w => ∏ i ∈ s, f i w)
        (z := z) hf_a hf_prod h0_a h0_prod

    have ih_unfold :
        deriv (fun w => ∏ i ∈ s, f i w) z / (∏ i ∈ s, f i z)
          = ∑ i ∈ s, deriv (f i) z / f i z := by
      have ih' := ih hf_s h0_s
      dsimp [logDerivC] at ih'
      exact ih'

    have hprod_insert :
        (fun w => ∏ i ∈ insert a s, f i w)
          = (fun w => f a w * (∏ i ∈ s, f i w)) := by
      funext w
      exact (Finset.prod_insert (s := s) (a := a) (f := fun i => f i w) ha)

    calc
      logDerivC (fun w => ∏ i ∈ insert a s, f i w) z
          = logDerivC (fun w => f a w * (∏ i ∈ s, f i w)) z := by
              rw [hprod_insert]
      _   = logDerivC (f a) z + logDerivC (fun w => ∏ i ∈ s, f i w) z := hmul
      _   = (deriv (f a) z / f a z) +
            (deriv (fun w => ∏ i ∈ s, f i w) z / (∏ i ∈ s, f i z)) := by
              rfl
      _   = (deriv (f a) z / f a z) + (∑ i ∈ s, deriv (f i) z / f i z) := by
              rw [ih_unfold]
      _   = ∑ i ∈ insert a s, deriv (f i) z / f i z := by
              simp [Finset.sum_insert, ha]
      _   = ∑ i ∈ insert a s, logDerivC (f i) z := by
              simp [logDerivC]

end EulerBasel



