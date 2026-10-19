/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# Ekeland's variational principle and critical points

Let `X` be a complete metric space and `f : X → ℝ` lower semicontinuous and bounded below.
Ekeland's principle says that for every `ε > 0` and every starting point `x₀` there is a point
`y` with `f y + ε * dist x₀ y ≤ f x₀` that is the strict minimizer of the perturbed function
`z ↦ f z + ε * dist z y`.

The proof follows the classical scheme. For each `x` the set
`S x = {z | f z + ε * dist z x ≤ f x}` contains `x`, is closed, and `z ∈ S x` implies
`S z ⊆ S x`. Starting from `x₀` we choose `x (n + 1) ∈ S (x n)` with value within `(1 / 2) ^ n`
of the infimum of `f` on `S (x n)`. Then `S (x (n + 1))` lies in a ball of radius
`(1 / 2) ^ n / ε` around `x (n + 1)`, so the sequence is Cauchy, its limit `y` lies in every
`S (x n)`, and `S y = {y}`.

Two consequences in a real Banach space `E` for a differentiable `f` bounded below:

* `exists_almost_critical`: for every `ε > 0` there is `u` with `f u ≤ inf f + ε` and
  `‖fderiv ℝ f u‖ ≤ ε`. One applies Ekeland at an `ε`-almost minimizer and differentiates the
  inequality `f y ≤ f (y + t • v) + ε * t * ‖v‖` as `t → 0⁺`.
* `exists_critical_point_of_palaisSmale`: if `f` satisfies the Palais-Smale condition at the
  level `c = inf f`, then `c` is attained at a point `u` with `fderiv ℝ f u = 0`.

## Main statements

* `Portfolio.ekeland`
* `Portfolio.exists_almost_critical`
* `Portfolio.exists_critical_point_of_palaisSmale`
-/

open Filter Topology Set Metric

@[expose] public section

namespace Portfolio

section Ekeland

variable {X : Type*} [MetricSpace X]

/-- The Ekeland set of `x`: points `z` with `f z + ε * dist z x ≤ f x`. -/
def ekelandSet (f : X → ℝ) (ε : ℝ) (x : X) : Set X :=
  {z | f z + ε * dist z x ≤ f x}

/-- Every point belongs to its own Ekeland set. -/
theorem mem_ekelandSet_self {f : X → ℝ} {ε : ℝ} {x : X} : x ∈ ekelandSet f ε x := by
  simp [ekelandSet]

/-- The Ekeland set of a lower semicontinuous function is closed. -/
theorem isClosed_ekelandSet {f : X → ℝ} (hf : LowerSemicontinuous f) (ε : ℝ) (x : X) :
    IsClosed (ekelandSet f ε x) :=
  (hf.add (continuous_const.mul (continuous_id.dist continuous_const)).lowerSemicontinuous)
    |>.isClosed_preimage (f x)

/-- Ekeland sets are nested: if `z ∈ S x` then `S z ⊆ S x`. -/
theorem ekelandSet_subset {f : X → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {x z : X}
    (hz : z ∈ ekelandSet f ε x) : ekelandSet f ε z ⊆ ekelandSet f ε x := by
  intro w hw
  change f z + ε * dist z x ≤ f x at hz
  change f w + ε * dist w z ≤ f z at hw
  change f w + ε * dist w x ≤ f x
  have := mul_le_mul_of_nonneg_left (dist_triangle w z x) hε
  linarith

/-- Inside an Ekeland set one can pick a point whose value is within `δ` of the infimum. -/
theorem exists_mem_ekelandSet_le {f : X → ℝ} (hb : BddBelow (range f)) (ε : ℝ) (x : X)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x' ∈ ekelandSet f ε x, ∀ z ∈ ekelandSet f ε x, f x' ≤ f z + δ := by
  have hne : (f '' ekelandSet f ε x).Nonempty := ⟨f x, x, mem_ekelandSet_self, rfl⟩
  have hbdd : BddBelow (f '' ekelandSet f ε x) := hb.mono (image_subset_range _ _)
  obtain ⟨_, ⟨x', hx', rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf (f '' ekelandSet f ε x)) hδ)
  refine ⟨x', hx', fun z hz => ?_⟩
  have := csInf_le hbdd (mem_image_of_mem f hz)
  linarith

/-- **Ekeland's variational principle** (strong form). For `f` lower semicontinuous and bounded
below on a complete metric space, `ε > 0` and any `x₀`, some `y` satisfies
`f y + ε * dist x₀ y ≤ f x₀` and strictly minimizes `z ↦ f z + ε * dist z y`. -/
theorem ekeland [CompleteSpace X] {f : X → ℝ} (hf : LowerSemicontinuous f)
    (hb : BddBelow (range f)) {ε : ℝ} (hε : 0 < ε) (x₀ : X) :
    ∃ y, f y + ε * dist x₀ y ≤ f x₀ ∧ ∀ z, z ≠ y → f y < f z + ε * dist z y := by
  set S := ekelandSet f ε
  choose next hnext_mem hnext_le using
    fun (n : ℕ) (x : X) => exists_mem_ekelandSet_le hb ε x (δ := (1 / 2 : ℝ) ^ n) (by positivity)
  let x : ℕ → X := fun n => Nat.rec (motive := fun _ => X) x₀ (fun k xk => next k xk) n
  have hxs : ∀ n, x (n + 1) = next n (x n) := fun n => rfl
  have hstep : ∀ n, x (n + 1) ∈ S (x n) := fun n => by rw [hxs]; exact hnext_mem _ _
  have hmono : ∀ n m, n ≤ m → S (x m) ⊆ S (x n) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact (ekelandSet_subset hε.le (hstep m)).trans ih
  have hrad : ∀ n, ∀ z ∈ S (x (n + 1)), ε * dist z (x (n + 1)) ≤ (1 / 2) ^ n := by
    intro n z hz
    have h1 : f (x (n + 1)) ≤ f z + (1 / 2) ^ n := by
      rw [hxs]; exact hnext_le n (x n) z (ekelandSet_subset hε.le (hstep n) hz)
    have h2 : f z + ε * dist z (x (n + 1)) ≤ f (x (n + 1)) := hz
    linarith
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro e he
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hε he) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨k + 1, fun n hn => ?_⟩
    have := hrad k (x n) (hmono _ _ hn mem_ekelandSet_self)
    exact lt_of_mul_lt_mul_left (this.trans_lt hk) hε.le
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hyS : ∀ n, y ∈ S (x n) := fun n =>
    (isClosed_ekelandSet hf ε (x n)).mem_of_tendsto hy
      (eventually_atTop.2 ⟨n, fun m hm => hmono n m hm mem_ekelandSet_self⟩)
  refine ⟨y, ?_, fun z hzy => ?_⟩
  · have h0 : f y + ε * dist y x₀ ≤ f x₀ := hyS 0
    rwa [dist_comm]
  · by_contra hcon
    have hzS : z ∈ S y := not_lt.mp hcon
    have hd : 0 < dist z y := dist_pos.2 hzy
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε * dist z y / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have h1 := hrad k z (ekelandSet_subset hε.le (hyS (k + 1)) hzS)
    have h2 := hrad k y (hyS (k + 1))
    have h3 := dist_triangle z (x (k + 1)) y
    rw [dist_comm (x (k + 1)) y] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 hε.le
    linarith

end Ekeland

section CriticalPoints

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `f y ≤ f z + ε * ‖z - y‖` for every `z`, then every directional derivative of `f` at `y`
is at least `-(ε * ‖v‖)`. -/
theorem neg_mul_norm_le_fderiv_apply {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) {ε : ℝ}
    (h : ∀ z, f y ≤ f z + ε * ‖z - y‖) (v : E) : -(ε * ‖v‖) ≤ fderiv ℝ f y v := by
  have hlim := (hf.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hz := h (y + t • v)
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le] at hz
  rw [smul_eq_mul, le_inv_mul_iff₀ ht]
  nlinarith

/-- Under the same hypothesis, the derivative of `f` at `y` has operator norm at most `ε`. -/
theorem norm_fderiv_le_of_forall_le {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ z, f y ≤ f z + ε * ‖z - y‖) : ‖fderiv ℝ f y‖ ≤ ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ hε fun v => ?_
  have h1 := neg_mul_norm_le_fderiv_apply hf h v
  have h2 := neg_mul_norm_le_fderiv_apply hf h (-v)
  rw [map_neg, norm_neg] at h2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **Approximate critical points.** A differentiable function bounded below on a Banach space
has, for every `ε > 0`, a point where it is `ε`-close to its infimum and its derivative has
norm at most `ε`. -/
theorem exists_almost_critical [CompleteSpace E] {f : E → ℝ} (hf : Differentiable ℝ f)
    (hb : BddBelow (range f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u, f u ≤ (⨅ x, f x) + ε ∧ ‖fderiv ℝ f u‖ ≤ ε := by
  obtain ⟨x₀, hx₀⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (⨅ x, f x) hε)
  obtain ⟨y, hy₁, hy₂⟩ := ekeland hf.continuous.lowerSemicontinuous hb hε x₀
  refine ⟨y, ?_, norm_fderiv_le_of_forall_le (hf y) hε.le fun z => ?_⟩
  · nlinarith [dist_nonneg (x := x₀) (y := y)]
  · rcases eq_or_ne z y with rfl | hzy
    · simp
    · rw [← dist_eq_norm]
      exact (hy₂ z hzy).le

/-- **Palais-Smale at the infimum.** Let `f` be differentiable and bounded below on a Banach
space, with infimum `c`. If every sequence with `f (u n) → c` and `fderiv ℝ f (u n) → 0` has a
convergent subsequence, then `c` is attained at a critical point of `f`. -/
theorem exists_critical_point_of_palaisSmale [CompleteSpace E] {f : E → ℝ}
    (hf : Differentiable ℝ f) (hb : BddBelow (range f))
    (hPS : ∀ u : ℕ → E, Tendsto (fun n => f (u n)) atTop (𝓝 (⨅ x, f x)) →
      Tendsto (fun n => ‖fderiv ℝ f (u n)‖) atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (u₀ : E), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 u₀)) :
    ∃ u, f u = ⨅ x, f x ∧ fderiv ℝ f u = 0 := by
  set c := ⨅ x, f x
  choose u hu₁ hu₂ using fun n : ℕ =>
    exists_almost_critical hf hb (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  have hlim := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 c) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => ciInf_le hb (u n)) hu₁
    simpa using tendsto_const_nhds.add hlim
  have hdu : Tendsto (fun n => ‖fderiv ℝ f (u n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hu₂ hlim
  obtain ⟨φ, u₀, hφ, hconv⟩ := hPS u hfu hdu
  have hval : f u₀ = c :=
    tendsto_nhds_unique ((hf.continuous.tendsto u₀).comp hconv) (hfu.comp hφ.tendsto_atTop)
  have hmin : IsLocalMin f u₀ :=
    Filter.Eventually.of_forall fun x => hval ▸ ciInf_le hb x
  exact ⟨u₀, hval, hmin.fderiv_eq_zero⟩

end CriticalPoints

end Portfolio

end
