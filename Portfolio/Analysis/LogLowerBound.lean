/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# A second order lower bound for `log (1 + x)`

For every `x ≥ 0` we have `x - x ^ 2 / 2 ≤ log (1 + x)`.

The proof studies `f t = log (1 + t) - t + t ^ 2 / 2`. Its derivative is
`1 / (1 + t) - 1 + t = t ^ 2 / (1 + t)`, which is nonnegative on `[0, ∞)`,
so `f` is monotone there and `f x ≥ f 0 = 0`.

See `notes/log-lower-bound.md` for a short informal write-up.
-/

open Real Set

@[expose] public section

namespace Portfolio

/-- The auxiliary function whose monotonicity gives the bound. -/
noncomputable def logGap (t : ℝ) : ℝ := Real.log (1 + t) - t + t ^ 2 / 2

/-- Derivative of `logGap` at any point with `1 + t > 0`. -/
theorem hasDerivAt_logGap {t : ℝ} (ht : 0 < 1 + t) :
    HasDerivAt logGap (t ^ 2 / (1 + t)) t := by
  have hlog : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s)) (1 / (1 + t)) t := by
    simpa using ((hasDerivAt_id t).const_add 1).log ht.ne'
  have hsq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
    simpa using (hasDerivAt_pow 2 t).div_const 2
  have h := (hlog.sub (hasDerivAt_id t)).add hsq
  have hfun : logGap = (fun s : ℝ ↦ Real.log (1 + s)) - id + fun s ↦ s ^ 2 / 2 := rfl
  have hval : t ^ 2 / (1 + t) = 1 / (1 + t) - 1 + t := by
    field_simp
    ring
  rw [hfun, hval]
  exact h

/-- `logGap` is monotone on `[0, ∞)`. -/
theorem logGap_monotoneOn : MonotoneOn logGap (Ici 0) := by
  have hpos : ∀ t ∈ Ici (0 : ℝ), 0 < 1 + t := fun t ht ↦ by
    have : (0 : ℝ) ≤ t := ht
    linarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (f' := fun t ↦ t ^ 2 / (1 + t))
  · exact fun t ht ↦ (hasDerivAt_logGap (hpos t ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (hasDerivAt_logGap (hpos t (mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht))))).hasDerivWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have h1 : 0 < 1 + t := hpos t (mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht)))
    exact div_nonneg (sq_nonneg t) h1.le

/-- **Main result.** For `x ≥ 0`, `x - x ^ 2 / 2 ≤ log (1 + x)`. -/
theorem sub_sq_div_two_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have h := logGap_monotoneOn (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr hx) hx
  simp only [logGap, add_zero, Real.log_one] at h
  linarith

end Portfolio

end
