/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# Time scale calculus on `ℤ` and `hℤ`

A *time scale* is a nonempty closed subset `T` of `ℝ` (Hilger, 1988). Calculus on a time scale
unifies differential equations (`T = ℝ`) and difference equations (`T = ℤ` or `T = hℤ`). Mathlib
has no time scale theory, so this file sets up the basic objects and works them out on the
discrete time scales `hℤ = {h n | n ∈ ℤ}` with `h > 0`.

## Main definitions

* `IsTimeScale T`: `T` is nonempty and closed.
* `forwardJump T t`: the forward jump operator `σ(t) = inf {s ∈ T | s > t}`, with the usual
  convention `σ(t) = t` when no point of `T` lies to the right of `t`.
* `graininess T t`: the graininess `μ(t) = σ(t) - t`.
* `deltaDeriv T f t`: the delta derivative `(f (σ t) - f t) / μ t` at a right-scattered point.
  At right-dense points the delta derivative is the ordinary derivative, which is not
  formalized here.
* `hilgerExp h p n`: the Hilger exponential `e_p(h n, 0) = ∏_{k < n} (1 + h p (h k))` on `hℤ`.

## Main results

* `forwardJump_hZ`, `graininess_hZ`, `deltaDeriv_hZ`: on `hℤ` one has `σ(t) = t + h`, `μ = h`
  and `f^Δ(t) = (f (t + h) - f t) / h`; on `ℤ` this is the forward difference (`deltaDeriv_int`).
* `hilgerExp_unique`, `eq_hilgerExp_of_deltaDeriv`: the Hilger exponential is the unique
  solution of the dynamic initial value problem `y^Δ = p y`, `y 0 = 1`.
* `hilgerExp_const_lt_exp`, `hilgerExp_one_one_ne_exp`: for constant `p` the Hilger exponential
  is `(1 + h p) ^ n`, which is strictly smaller than `exp (p t)`; for example `2 ≠ e`.
* `tendsto_hilgerExp_exp`: as the graininess `h = t / N` tends to zero, `(1 + p t / N) ^ N`
  tends to `exp (p t)`, so the continuous exponential is recovered in the limit.
* `hZ_induction`: the time scale induction principle on `{h n | n ∈ ℕ}`.
-/

open Real Set Filter Topology

@[expose] public section

namespace Portfolio

/-! ### Time scales and the jump operators -/

/-- A time scale is a nonempty closed subset of `ℝ`. -/
def IsTimeScale (T : Set ℝ) : Prop :=
  T.Nonempty ∧ IsClosed T

open scoped Classical in
/-- The forward jump operator `σ(t) = inf {s ∈ T | t < s}`. When no point of `T` lies strictly to
the right of `t` (for instance at the maximum of `T`), the convention is `σ(t) = t`. -/
noncomputable def forwardJump (T : Set ℝ) (t : ℝ) : ℝ :=
  if {s ∈ T | t < s}.Nonempty then sInf {s ∈ T | t < s} else t

/-- The graininess `μ(t) = σ(t) - t`, the distance from `t` to the next point of `T`. -/
noncomputable def graininess (T : Set ℝ) (t : ℝ) : ℝ :=
  forwardJump T t - t

/-- A point `t` is right-scattered when `t < σ(t)`, i.e. the time scale has a gap to its right. -/
def IsRightScattered (T : Set ℝ) (t : ℝ) : Prop :=
  t < forwardJump T t

/-- The delta derivative at a right-scattered point, `f^Δ(t) = (f (σ t) - f t) / μ(t)`.
This is the correct value only when `t` is right-scattered. At right-dense points (`μ(t) = 0`) the
delta derivative is the ordinary derivative, a limit that is not formalized here, and this
expression is a junk value (`0`, by division by zero). -/
noncomputable def deltaDeriv (T : Set ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f (forwardJump T t) - f t) / graininess T t

/-- The forward jump never moves to the left: `t ≤ σ(t)`. -/
theorem le_forwardJump (T : Set ℝ) (t : ℝ) : t ≤ forwardJump T t := by
  unfold forwardJump
  split_ifs with hne
  · exact le_csInf hne fun s hs ↦ hs.2.le
  · exact le_rfl

/-- The graininess is nonnegative. -/
theorem graininess_nonneg (T : Set ℝ) (t : ℝ) : 0 ≤ graininess T t :=
  sub_nonneg.mpr (le_forwardJump T t)

/-! ### The time scale `hℤ` -/

/-- The time scale `hℤ = {h n | n ∈ ℤ}` of integer multiples of `h`. -/
def hZ (h : ℝ) : Set ℝ :=
  Set.range fun n : ℤ ↦ h * n

/-- `hℤ` is a time scale for every `h` (for `h = 0` it is the single point `0`). -/
theorem isTimeScale_hZ (h : ℝ) : IsTimeScale (hZ h) :=
  ⟨⟨0, 0, by simp⟩,
    ((isClosedMap_smul₀ h).comp Int.isClosedEmbedding_coe_real.isClosedMap).isClosed_range⟩

/-- In `hℤ` with `h > 0`, the least point strictly to the right of `h n` is `h n + h`. -/
theorem isLeast_hZ {h : ℝ} (hh : 0 < h) (n : ℤ) :
    IsLeast {s ∈ hZ h | h * n < s} (h * n + h) := by
  refine ⟨⟨⟨n + 1, by push_cast; ring⟩, by linarith⟩, ?_⟩
  rintro s ⟨⟨m, rfl⟩, hs⟩
  have hnm : (n : ℝ) < m := lt_of_mul_lt_mul_left hs hh.le
  have hnm' : (n : ℝ) + 1 ≤ m := by exact_mod_cast Int.add_one_le_of_lt (by exact_mod_cast hnm)
  nlinarith

/-- On `hℤ` with `h > 0` the forward jump is `σ(h n) = h n + h`. -/
theorem forwardJump_hZ {h : ℝ} (hh : 0 < h) (n : ℤ) :
    forwardJump (hZ h) (h * n) = h * n + h := by
  have hl := isLeast_hZ hh n
  rw [forwardJump, ite_eq_left ⟨_, hl.1⟩, hl.csInf_eq]

/-- On `hℤ` with `h > 0` the graininess is constant: `μ(h n) = h`. -/
theorem graininess_hZ {h : ℝ} (hh : 0 < h) (n : ℤ) : graininess (hZ h) (h * n) = h := by
  rw [graininess, forwardJump_hZ hh]
  ring

/-- Every point of `hℤ` with `h > 0` is right-scattered. -/
theorem isRightScattered_hZ {h : ℝ} (hh : 0 < h) (n : ℤ) : IsRightScattered (hZ h) (h * n) := by
  rw [IsRightScattered, forwardJump_hZ hh]
  linarith

/-- On `hℤ` the delta derivative is the difference quotient `(f (t + h) - f t) / h`. -/
theorem deltaDeriv_hZ {h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) (n : ℤ) :
    deltaDeriv (hZ h) f (h * n) = (f (h * n + h) - f (h * n)) / h := by
  rw [deltaDeriv, forwardJump_hZ hh, graininess_hZ hh]

/-- `ℤ`, seen as a subset of `ℝ`, is the time scale `hℤ` with `h = 1`. -/
theorem hZ_one : hZ 1 = Set.range ((↑) : ℤ → ℝ) := by
  simp [hZ]

/-- On `ℤ` the delta derivative is the forward difference `f (n + 1) - f n`. -/
theorem deltaDeriv_int (f : ℝ → ℝ) (n : ℤ) :
    deltaDeriv (Set.range ((↑) : ℤ → ℝ)) f n = f (n + 1) - f n := by
  have := deltaDeriv_hZ one_pos f n
  rw [hZ_one] at this
  simpa using this

/-! ### The Hilger exponential on `hℤ` -/

/-- The Hilger exponential `e_p(h n, 0) = ∏_{k < n} (1 + h p (h k))` on `hℤ`, started at time `0`
and evaluated at the time `t = h n` with `n : ℕ`. -/
noncomputable def hilgerExp (h : ℝ) (p : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + h * p (h * k))

/-- The Hilger exponential starts at `1`. -/
@[simp]
theorem hilgerExp_zero (h : ℝ) (p : ℝ → ℝ) : hilgerExp h p 0 = 1 := by
  simp [hilgerExp]

/-- One step of the Hilger exponential multiplies by `1 + μ p = 1 + h p (h n)`. -/
theorem hilgerExp_succ (h : ℝ) (p : ℝ → ℝ) (n : ℕ) :
    hilgerExp h p (n + 1) = (1 + h * p (h * n)) * hilgerExp h p n := by
  rw [hilgerExp, Finset.prod_range_succ, mul_comm]
  rfl

/-- The Hilger exponential solves `y^Δ = p y`, written as a difference quotient on `hℤ`. -/
theorem hilgerExp_dynamic {h : ℝ} (hh : h ≠ 0) (p : ℝ → ℝ) (n : ℕ) :
    (hilgerExp h p (n + 1) - hilgerExp h p n) / h = p (h * n) * hilgerExp h p n := by
  rw [hilgerExp_succ, div_eq_iff hh]
  ring

/-- Uniqueness: a sequence `y` with `y 0 = 1` and `(y (n + 1) - y n) / h = p (h n) y n` is the
Hilger exponential. -/
theorem hilgerExp_unique {h : ℝ} (hh : h ≠ 0) (p : ℝ → ℝ) (y : ℕ → ℝ) (h0 : y 0 = 1)
    (hy : ∀ n : ℕ, (y (n + 1) - y n) / h = p (h * n) * y n) : y = hilgerExp h p := by
  funext n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have key := hy n
    rw [div_eq_iff hh] at key
    rw [hilgerExp_succ, ← ih]
    linear_combination key

/-- The same uniqueness in time scale language: if `y : ℝ → ℝ` satisfies `y^Δ = p y` on
`{h n | n ∈ ℕ}` and `y 0 = 1`, then `y (h n)` is the Hilger exponential. -/
theorem eq_hilgerExp_of_deltaDeriv {h : ℝ} (hh : 0 < h) (p y : ℝ → ℝ) (h0 : y 0 = 1)
    (hy : ∀ n : ℕ, deltaDeriv (hZ h) y (h * n) = p (h * n) * y (h * n)) (n : ℕ) :
    y (h * n) = hilgerExp h p n := by
  have := hilgerExp_unique hh.ne' p (fun n : ℕ ↦ y (h * n)) (by simpa using h0) ?_
  · exact congrFun this n
  intro k
  have hk := hy k
  have hd := deltaDeriv_hZ hh y k
  push_cast at hd
  rw [hd] at hk
  push_cast
  rwa [mul_add, mul_one]

/-- Conversely, the Hilger exponential (extended to `ℝ` in any way) satisfies `y^Δ = p y` on
`{h n | n ∈ ℕ}`, phrased with `deltaDeriv`. -/
theorem deltaDeriv_hilgerExp {h : ℝ} (hh : 0 < h) (p y : ℝ → ℝ)
    (hy : ∀ n : ℕ, y (h * n) = hilgerExp h p n) (n : ℕ) :
    deltaDeriv (hZ h) y (h * n) = p (h * n) * y (h * n) := by
  have hd := deltaDeriv_hZ hh y n
  push_cast at hd
  have hs : h * (n : ℝ) + h = h * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hd, hs, hy, hy, hilgerExp_dynamic hh.ne']

/-! ### Constant coefficients and comparison with `exp` -/

/-- For a constant coefficient `c` the Hilger exponential is the power `(1 + h c) ^ n`. -/
theorem hilgerExp_const (h c : ℝ) (n : ℕ) : hilgerExp h (fun _ ↦ c) n = (1 + h * c) ^ n := by
  simp [hilgerExp]

/-- The Hilger exponential is not the real exponential: on `ℤ` with `p = 1`, at time `1` it equals
`2`, while `exp 1 = e`. -/
theorem hilgerExp_one_one_ne_exp : hilgerExp 1 (fun _ ↦ 1) 1 = 2 ∧
    hilgerExp 1 (fun _ ↦ 1) 1 ≠ exp (1 * (1 * 1)) := by
  have h2 : hilgerExp 1 (fun _ ↦ 1) 1 = 2 := by
    rw [hilgerExp_const]
    norm_num
  refine ⟨h2, ?_⟩
  rw [h2]
  have := exp_one_gt_d9
  norm_num at this ⊢
  linarith

/-- For constant `c` with `h c ≠ 0` and `1 + h c ≥ 0`, the Hilger exponential at time `t = h n`,
`n ≥ 1`, is strictly below `exp (c t)`, since `1 + x < exp x` for `x ≠ 0`. -/
theorem hilgerExp_const_lt_exp {h c : ℝ} (hc : h * c ≠ 0) (hc' : -1 ≤ h * c) {n : ℕ}
    (hn : n ≠ 0) : hilgerExp h (fun _ ↦ c) n < exp (c * (h * n)) := by
  rw [hilgerExp_const, show c * (h * n) = n * (h * c) by ring, exp_nat_mul]
  exact pow_lt_pow_left₀ (by linarith [add_one_lt_exp hc]) (by linarith) hn

/-! ### The continuum limit -/

/-- Continuum limit: with graininess `h = t / N`, the time `t = h N` is fixed and the Hilger
exponential `(1 + c t / N) ^ N` tends to `exp (c t)` as `N → ∞`, i.e. as `h → 0`. -/
theorem tendsto_hilgerExp_exp (c t : ℝ) :
    Tendsto (fun N : ℕ ↦ hilgerExp (t / N) (fun _ ↦ c) N) atTop (𝓝 (exp (c * t))) := by
  refine (tendsto_one_add_div_pow_exp (c * t)).congr fun N ↦ ?_
  rw [hilgerExp_const]
  ring

/-! ### Induction on `hℤ` -/

/-- Time scale induction on `{h n | n ∈ ℕ}`: if `P 0` holds and `P t` implies `P (σ t)` at every
right-scattered point `t` of `hℤ`, then `P` holds at every `h n` with `n : ℕ`. -/
theorem hZ_induction {h : ℝ} (hh : 0 < h) (P : ℝ → Prop) (h0 : P 0)
    (hstep : ∀ t ∈ hZ h, IsRightScattered (hZ h) t → P t → P (forwardJump (hZ h) t)) :
    ∀ n : ℕ, P (h * n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hmem : h * (n : ℝ) ∈ hZ h := ⟨n, by simp⟩
    have hrs := isRightScattered_hZ hh n
    have hj := forwardJump_hZ hh n
    push_cast at hrs hj
    have := hstep _ hmem hrs ih
    rw [hj] at this
    push_cast
    rwa [mul_add, mul_one]

end Portfolio

end
