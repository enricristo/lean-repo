/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Portfolio.PLaplacian.PiP

/-!
# Closed form of π_p

For every `p > 1`,

  `π_p = 2 ∫₀¹ (1 - s ^ p) ^ (-1 / p) ds = 2 π / (p sin (π / p))`.

The proof has three steps.

1. `piIntegral_eq_beta`: the substitution `u = s ^ p` turns the integral into
   `(1 / p) ∫₀¹ u ^ (1/p - 1) (1 - u) ^ (-1/p) du`, a Beta integral `B(1/p, 1 - 1/p) / p`.
2. `integral_beta_one_sub`: `B(a, 1 - a) = Γ(a) Γ(1 - a) / Γ(1) = π / sin (π a)`, by Mathlib's
   relation between Beta and Gamma and Euler's reflection formula.
3. `piIntegral_eq`, `piP_eq`: algebra.

See `notes/pi-p.md` for the informal write-up.
-/

open Real Set intervalIntegral MeasureTheory

@[expose] public section

namespace Portfolio

/-- The real Beta integral `∫₀¹ u ^ (a - 1) (1 - u) ^ (-a) du` equals `π / sin (π a)`
for `0 < a < 1`. This is `B(a, 1 - a) = Γ(a) Γ(1 - a)` and Euler's reflection formula. -/
theorem integral_beta_one_sub {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (-a) = π / Real.sin (π * a) := by
  have hcpx : ((∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (-a) : ℝ) : ℂ)
      = Complex.betaIntegral a (1 - a) := by
    rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    refine integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le zero_le_one] at hu
    have h1 : (0 : ℝ) ≤ 1 - u := by linarith [hu.2]
    push_cast
    rw [Complex.ofReal_cpow hu.1, Complex.ofReal_cpow h1]
    push_cast
    ring_nf
  have hgamma := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := 1 - (a : ℂ))
    (by simpa using ha0) (by simpa using ha1)
  rw [add_sub_cancel, Complex.Gamma_one, one_mul, Complex.Gamma_mul_Gamma_one_sub] at hgamma
  have : ((π / Real.sin (π * a) : ℝ) : ℂ) = Complex.betaIntegral a (1 - a) := by
    rw [← hgamma]
    push_cast
    rfl
  exact_mod_cast hcpx.trans this.symm

/-- **Substitution** `u = s ^ p`: the integral behind `π_p` is a Beta integral.
It runs through Mathlib's substitution on `(0, ∞)`, with the integrand cut off at `1` by an
indicator function, so no limit at the singular endpoints is ever taken. -/
theorem piIntegral_eq_beta {p : ℝ} (hp : 1 < p) :
    piIntegral p = (1 / p) * ∫ u in (0 : ℝ)..1, u ^ (1 / p - 1) * (1 - u) ^ (-(1 / p)) := by
  have hp0 : 0 < p := by linarith
  set a := 1 / p with ha
  have hpa : p * a = 1 := by rw [ha]; field_simp
  set g : ℝ → ℝ := (Iio (1 : ℝ)).indicator (fun y ↦ a * (y ^ (a - 1) * (1 - y) ^ (-a))) with hg
  have key := integral_comp_rpow_Ioi_of_pos (g := g) hp0
  have hR : ∫ y in Ioi 0, g y = a * ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (-a) := by
    rw [hg, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      MeasureTheory.integral_const_mul, integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  have hL : ∫ x in Ioi 0, (p * x ^ (p - 1)) • g (x ^ p) = piIntegral p := by
    rw [piIntegral, integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← Ioi_inter_Iio,
      ← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx0 : 0 < x := hx
    by_cases hx1 : x < 1
    · have hxp : x ^ p < 1 := rpow_lt_one hx0.le hx1 hp0
      rw [hg, smul_eq_mul, indicator_of_mem (show x ^ p ∈ Iio (1 : ℝ) from hxp),
        indicator_of_mem (show x ∈ Iio (1 : ℝ) from hx1)]
      have hexp : (p - 1) + p * (a - 1) = 0 := by rw [mul_sub, hpa]; ring
      calc p * x ^ (p - 1) * (a * ((x ^ p) ^ (a - 1) * (1 - x ^ p) ^ (-a)))
          = (p * a) * (x ^ (p - 1) * x ^ (p * (a - 1))) * (1 - x ^ p) ^ (-a) := by
            rw [← rpow_mul hx0.le]; ring
        _ = (1 - x ^ p) ^ (-a) := by rw [hpa, ← rpow_add hx0, hexp, rpow_zero]; ring
    · have hxp : ¬ x ^ p < 1 := not_lt.mpr (one_le_rpow (not_lt.mp hx1) hp0.le)
      rw [hg, smul_eq_mul, indicator_of_notMem (show x ^ p ∉ Iio (1 : ℝ) from hxp),
        indicator_of_notMem (show x ∉ Iio (1 : ℝ) from hx1), mul_zero]
  rw [← hL, key, hR]

/-- **Closed form.** For `p > 1`, `∫₀¹ (1 - s ^ p) ^ (-1 / p) ds = π / (p sin (π / p))`. -/
theorem piIntegral_eq {p : ℝ} (hp : 1 < p) : piIntegral p = π / (p * Real.sin (π / p)) := by
  have hp0 : 0 < p := by linarith
  have ha1 : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
  rw [piIntegral_eq_beta hp, integral_beta_one_sub (by positivity) ha1, mul_one_div]
  ring

/-- **Main result.** For `p > 1`, `π_p = 2 π / (p sin (π / p))`. -/
theorem piP_eq {p : ℝ} (hp : 1 < p) : piP p = 2 * π / (p * Real.sin (π / p)) := by
  rw [piP, piIntegral_eq hp]
  ring

end Portfolio

end
