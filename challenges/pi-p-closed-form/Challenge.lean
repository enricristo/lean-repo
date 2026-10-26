import Mathlib

namespace Ambrosio

noncomputable section

open Real

namespace PLaplacian

/-- The constant `π_p` of the one-dimensional `p`-Laplacian, in Lindqvist's normalization:
the first Dirichlet eigenvalue of `-(|u'|^(p-2) u')' = λ |u|^(p-2) u` on `(0, 1)` is
`(p - 1) π_p ^ p`. The integral is improper at `s = 1`; as a Lebesgue integral it is finite. -/
def piP (p : ℝ) : ℝ := 2 * ∫ s in (0 : ℝ)..1, (1 - s ^ p) ^ (-(1 / p))

/-- For `p = 2` the constant is `π`. -/
theorem piP_two : piP 2 = π := by
  sorry

/-- Closed form for every `p > 1`. -/
theorem piP_closed_form (p : ℝ) (hp : 1 < p) :
    piP p = 2 * π / (p * Real.sin (π / p)) := by
  sorry

end PLaplacian

end

end Ambrosio
