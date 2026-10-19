/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# The Dirac delta is not a regular distribution

A distribution `T` on `ℝ` is *regular* if there is a locally integrable `f` with
`T φ = ∫ f φ` for every test function `φ` (smooth with compact support). The Dirac delta
`δ φ = φ 0` is the standard example of a distribution that is not regular. This was a question
in the author's PDE exam (P2 de EDP, 2021).

The statement `dirac_not_regular` uses only plain Mathlib notions (`LocallyIntegrable`,
`ContDiff ℝ ∞`, `HasCompactSupport`), so it can be read without any theory of distributions.
Note that `∞` means `C^∞`; the top element `ω` of `WithTop ℕ∞` would mean analytic, and an
analytic function with compact support vanishes, which would make the statement false.

## Proof idea

Suppose `f` represents `δ`. Take a bump `φ_ε` with `φ_ε 0 = 1`, `0 ≤ φ_ε ≤ 1` and support in
the ball of radius `ε`. Then `1 = φ_ε 0 = ∫ f φ_ε ≤ ∫_{B(0, ε)} |f|`. The balls `B̄(0, 1/(n+1))`
decrease to `{0}`, a null set, so `∫_{B̄(0, 1/(n+1))} |f| → 0` (`tendsto_setIntegral_of_antitone`),
a contradiction. The argument works verbatim for any finite dimensional space with a measure
that gives no mass to points, which also gives the version on `ℝⁿ` for `n ≥ 1`. For `n = 0` the
space is a point and `δ` is regular (take `f = 1`), so the hypothesis `n ≠ 0` is needed.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

@[expose] public section

namespace Portfolio

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bump function used in the proof: equal to `1` on `B̄(0, ε / 2)`, supported in
`B(0, ε)`. -/
noncomputable def diracBump {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : E) :=
  ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩

/-- The bump `diracBump hε` takes the value `1` at the origin. -/
theorem diracBump_zero [HasContDiffBump E] {ε : ℝ} (hε : 0 < ε) :
    (diracBump (E := E) hε) 0 = 1 :=
  (diracBump hε).one_of_mem_closedBall (mem_closedBall_self (half_pos hε).le)

/-- The support of `diracBump hε` is exactly the open ball `B(0, ε)`. -/
theorem support_diracBump [HasContDiffBump E] {ε : ℝ} (hε : 0 < ε) :
    Function.support (diracBump (E := E) hε) = ball 0 ε :=
  (diracBump hε).support_eq

/-- On `ℝ`, the bump `diracBump hε` equals `1` at `0` and its support is `(-ε, ε)`. -/
theorem diracBump_real {ε : ℝ} (hε : 0 < ε) :
    diracBump (E := ℝ) hε 0 = 1 ∧ Function.support (diracBump (E := ℝ) hε) = Ioo (-ε) ε := by
  refine ⟨diracBump_zero hε, ?_⟩
  rw [support_diracBump, Real.ball_eq_Ioo, zero_sub, zero_add]

omit [NormedSpace ℝ E] in
/-- The closed balls `B̄(0, 1 / (n + 1))` shrink to the origin. -/
theorem iInter_closedBall_one_div :
    ⋂ n : ℕ, closedBall (0 : E) (1 / (n + 1)) = {0} := by
  ext x
  simp only [mem_iInter, mem_closedBall, dist_zero_right, mem_singleton_iff]
  refine ⟨fun h ↦ norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg x)), fun h n ↦ ?_⟩
  · refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    linarith [h n]
  · rw [h, norm_zero]
    positivity

/-- For a locally integrable `f` and a measure giving no mass to points, `∫_{B̄(0, r)} ‖f‖`
can be made smaller than any `η > 0` by taking `r` of the form `1 / (n + 1)`. -/
theorem exists_setIntegral_norm_closedBall_lt [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [NullSingletonClass μ] {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∫ x in closedBall (0 : E) (1 / (n + 1)), ‖f x‖ ∂μ < η := by
  have hanti : Antitone fun n : ℕ ↦ closedBall (0 : E) (1 / (n + 1)) := by
    intro m n hmn
    apply closedBall_subset_closedBall
    gcongr
  have hlim := tendsto_setIntegral_of_antitone (μ := μ) (f := fun x ↦ ‖f x‖)
    (fun _ ↦ measurableSet_closedBall) hanti
    ⟨0, (hf.integrableOn_isCompact (isCompact_closedBall _ _)).norm⟩
  rw [iInter_closedBall_one_div, setIntegral_measure_zero _ (measure_singleton 0)] at hlim
  exact (hlim.eventually (gt_mem_nhds hη)).exists

/-- The Dirac delta is not a regular distribution, in any finite dimensional real normed space
carrying a measure that gives no mass to points: no locally integrable `f` satisfies
`∫ f φ dμ = φ 0` for every smooth compactly supported `φ`. -/
theorem dirac_not_regular_of_nullSingleton [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [NullSingletonClass μ] :
    ¬ ∃ f : E → ℝ, LocallyIntegrable f μ ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ x, f x * φ x ∂μ = φ 0 := by
  rintro ⟨f, hf, hδ⟩
  obtain ⟨n, hn⟩ := exists_setIntegral_norm_closedBall_lt (μ := μ) hf one_pos
  set r : ℝ := 1 / (n + 1)
  have hr : 0 < r := by positivity
  set φ := diracBump (E := E) hr
  have hφ : ∫ x, f x * φ x ∂μ = 1 := by
    rw [hδ φ φ.contDiff φ.hasCompactSupport, diracBump_zero]
  have hout : ∀ x, x ∉ closedBall (0 : E) r → f x * φ x = 0 := by
    intro x hx
    have : φ x = 0 := Function.notMem_support.mp fun h ↦
      hx (ball_subset_closedBall (by rwa [support_diracBump] at h))
    rw [this, mul_zero]
  have hle : ‖∫ x in closedBall (0 : E) r, f x * φ x ∂μ‖ ≤
      ∫ x in closedBall (0 : E) r, ‖f x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (hf.integrableOn_isCompact (isCompact_closedBall _ _)).norm
      (Eventually.of_forall fun x ↦ ?_))
    simp only [norm_mul, Real.norm_of_nonneg φ.nonneg]
    exact mul_le_of_le_one_right (norm_nonneg _) φ.le_one
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout, hφ, norm_one] at hle
  linarith

/-- **The Dirac delta is not a regular distribution.** There is no locally integrable
`f : ℝ → ℝ` with `∫ f φ = φ 0` for every smooth compactly supported test function `φ`. -/
theorem dirac_not_regular :
    ¬ ∃ f : ℝ → ℝ, LocallyIntegrable f ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ x, f x * φ x = φ 0 :=
  dirac_not_regular_of_nullSingleton volume

/-- The Dirac delta on `ℝⁿ` is not a regular distribution when `n ≠ 0`. -/
theorem dirac_not_regular_euclidean {n : ℕ} (hn : n ≠ 0) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyIntegrable f ∧
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ x, f x * φ x = φ 0 := by
  have : NeZero n := ⟨hn⟩
  exact dirac_not_regular_of_nullSingleton volume

end Portfolio

end
