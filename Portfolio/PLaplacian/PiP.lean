/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# The constant π_p of the one dimensional p-Laplacian

For `p > 1`, the first eigenfunction of `-(|u'|^{p-2} u')' = λ |u|^{p-2} u` on an interval is a
generalized sine, and its half period is governed by the integral

  `I p = ∫₀¹ (1 - s ^ p) ^ (-1 / p) ds`.

For `p = 2` the integrand is `1 / √(1 - s ^ 2)`, the derivative of `arcsin`, and `I 2 = π / 2`.
This file starts with that case. The integral is improper at `s = 1`, and the proof handles that
without computing any limit: a function whose derivative is nonnegative has an integrable
derivative (`integrableOn_deriv_of_nonneg`).
-/

open Real Set intervalIntegral MeasureTheory

@[expose] public section

namespace Portfolio

/-- The integral `∫₀¹ (1 - s ^ p) ^ (-1 / p) ds` behind `π_p`. -/
noncomputable def piIntegral (p : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s ^ p) ^ (-(1 / p))

/-- `∫₀¹ 1 / √(1 - s²) ds = π / 2`, an improper integral computed with `arcsin`. -/
theorem integral_one_div_sqrt_one_sub_sq :
    ∫ s in (0 : ℝ)..1, 1 / √(1 - s ^ 2) = π / 2 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt arcsin (1 / √(1 - x ^ 2)) x := fun x hx ↦
    hasDerivAt_arcsin (ne_of_gt (by linarith [hx.1])) (ne_of_lt hx.2)
  have hcont : ContinuousOn arcsin (Icc 0 1) := continuous_arcsin.continuousOn
  have hint : IntervalIntegrable (fun s : ℝ ↦ 1 / √(1 - s ^ 2)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrableOn_deriv_of_nonneg hcont hderiv (fun x _ ↦ by positivity)
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint, arcsin_one, arcsin_zero,
    sub_zero]

/-- For `p = 2` the general integrand is `1 / √(1 - s²)`. -/
theorem piIntegral_two_integrand {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 - s ^ (2 : ℝ)) ^ (-(1 / (2 : ℝ))) = 1 / √(1 - s ^ 2) := by
  have h0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  rw [rpow_two, rpow_neg h0, sqrt_eq_rpow]
  exact (one_div _).symm

/-- **Main result.** `I 2 = π / 2`. -/
theorem piIntegral_two : piIntegral 2 = π / 2 := by
  unfold piIntegral
  rw [← integral_one_div_sqrt_one_sub_sq]
  refine integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact piIntegral_two_integrand hs

end Portfolio

end
