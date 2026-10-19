/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# A telescoping series

We prove `∑_{n ≥ 1} 1 / (n (n + 1) (n + 2)) = 1 / 4`.

Lean sums over `ℕ` start at `0`, so the series is indexed by `n + 1`:
the general term is `1 / ((n + 1) (n + 2) (n + 3))`.

The key identity is
`1 / (n (n + 1) (n + 2)) = (1 / 2) (1 / (n (n + 1)) - 1 / ((n + 1) (n + 2)))`,
which gives the closed form of the partial sums
`∑_{n = 1}^{N} = 1 / 4 - 1 / (2 (N + 1) (N + 2))`.
The correction term goes to `0`, so the series converges to `1 / 4`.

See `notes/telescoping-sum.md` for a short informal write-up.
-/

open Finset Filter Topology

@[expose] public section

namespace Portfolio

/-- The general term, shifted so that the sum starts at `n = 0`. -/
noncomputable def telescopingTerm (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))

/-- The terms are nonnegative. -/
theorem telescopingTerm_nonneg (n : ℕ) : 0 ≤ telescopingTerm n := by
  unfold telescopingTerm
  positivity

/-- Closed form of the partial sums. -/
theorem sum_telescopingTerm (N : ℕ) :
    ∑ n ∈ range N, telescopingTerm n
      = 1 / 4 - 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih, telescopingTerm]
    push_cast
    field_simp
    ring

/-- The correction term `1 / (2 (N + 1) (N + 2))` tends to `0`. -/
theorem tendsto_correction :
    Tendsto (fun N : ℕ ↦ 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2))) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N ↦ by positivity) (fun N ↦ ?_)
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  apply one_div_le_one_div_of_le h1
  nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]

/-- **Main result** in `HasSum` form. -/
theorem hasSum_telescopingTerm : HasSum telescopingTerm (1 / 4) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg telescopingTerm_nonneg]
  simp_rw [sum_telescopingTerm]
  simpa using (tendsto_const_nhds (x := (1 / 4 : ℝ))).sub tendsto_correction

/-- **Main result.** `∑_{n ≥ 1} 1 / (n (n + 1) (n + 2)) = 1 / 4`. -/
theorem tsum_telescopingTerm : ∑' n : ℕ, telescopingTerm n = 1 / 4 :=
  hasSum_telescopingTerm.tsum_eq

end Portfolio

end
