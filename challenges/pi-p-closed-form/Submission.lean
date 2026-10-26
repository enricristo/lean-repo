import Mathlib

namespace Ambrosio

noncomputable section

open Real

namespace PLaplacian

/-- The constant `π_p` of the one-dimensional `p`-Laplacian, in Lindqvist's normalization:
the first Dirichlet eigenvalue of `-(|u'|^(p-2) u')' = λ |u|^(p-2) u` on `(0, 1)` is
`(p - 1) π_p ^ p`. The integral is improper at `s = 1`; as a Lebesgue integral it is finite. -/
def piP (p : ℝ) : ℝ := 2 * ∫ s in (0 : ℝ)..1, (1 - s ^ p) ^ (-(1 / p))

open Set intervalIntegral MeasureTheory

/-! ## Proofs

Ported from `Portfolio/PLaplacian/PiP.lean` and `ClosedForm.lean` in
https://github.com/enricristo/lean-repo. -/

/-- The integral behind `π_p`. -/
def piIntegral (p : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s ^ p) ^ (-(1 / p))

theorem piP_eq_two_mul (p : ℝ) : piP p = 2 * piIntegral p := rfl

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

/-- `I 2 = π / 2`. -/
theorem piIntegral_two : piIntegral 2 = π / 2 := by
  unfold piIntegral
  rw [← integral_one_div_sqrt_one_sub_sq]
  refine integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact piIntegral_two_integrand hs

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

theorem piP_two : piP 2 = π := by
  rw [piP_eq_two_mul, piIntegral_two]
  ring

theorem piP_closed_form (p : ℝ) (hp : 1 < p) :
    piP p = 2 * π / (p * Real.sin (π / p)) := by
  rw [piP_eq_two_mul, piIntegral_eq hp]
  ring

end PLaplacian

end

end Ambrosio
