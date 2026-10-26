/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# A seven-coloring of the plane

The plane can be colored with seven colors so that no two points at distance exactly `1` get
the same color. This is the upper bound `χ(ℝ²) ≤ 7` in the Hadwiger–Nelson problem
(Isbell, 1950).

The statement is the task `plane-coloring` of the openai-math Lean environments
(FineEnvs packaging of OpenAI's openai/math release, family 158). The same proof, in the exact
file format the task's grader receives, is in `challenges/openai-math-plane-coloring/`.

The classical construction uses hexagons. This one uses bricks, because a brick is cut out by
two floor functions and every step becomes a linear inequality.

## Main statements

* `Portfolio.PlaneColoring.brickColor`: the coloring.
* `Portfolio.PlaneColoring.properColoring_seven`: it is proper.
-/

@[expose] public section

noncomputable section

namespace Portfolio.PlaneColoring

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A proper coloring with `k` colors: points at distance `1` get different colors. -/
def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y

/-! ## The bricks

The plane is tiled by half-open bricks `[0, 4/5) × [0, 3/5)`. Row `j` occupies
`3j/5 ≤ y < 3(j+1)/5`, and is shifted to the right by `2/5` of a brick relative to row `j - 1`,
so brick `i` of row `j` occupies `4i/5 + 8j/25 ≤ x < 4i/5 + 8j/25 + 4/5`. Brick `(i, j)` gets
color `(i + 5j) mod 7`.

* Two points of the same brick are at distance `< 1`: the brick's diagonal is exactly `1`
  (`(4/5)² + (3/5)² = 1`) and the brick is half-open.
* Two distinct bricks of the same color are at distance `> 1`. If two points are at distance
  `1`, their rows differ by at most `2` and their bricks by at most `3`, and among those offsets
  the only ones with `di + 5 dj ≡ 0 (mod 7)` are `(±2, ±1)` and `(∓3, ±2)`. For these the gap
  between the bricks is at least `√(784/625) = 28/25`.
-/

/-- The row of the brick containing `p`. -/
def brickRow (p : Plane) : ℤ := ⌊5 * p 1 / 3⌋

/-- The position of the brick containing `p` inside its row. -/
def brickCol (p : Plane) : ℤ := ⌊5 * p 0 / 4 - 2 * (brickRow p : ℝ) / 5⌋

/-- The color of brick `(i, j)` is `(i + 5 j) mod 7`. -/
def brickColor (p : Plane) : Fin 7 :=
  ⟨((brickCol p + 5 * brickRow p) % 7).toNat, by omega⟩

theorem brickRow_bounds (p : Plane) :
    3 * (brickRow p : ℝ) / 5 ≤ p 1 ∧ p 1 < 3 * (brickRow p : ℝ) / 5 + 3 / 5 := by
  have h1 := Int.floor_le (5 * p 1 / 3)
  have h2 := Int.lt_floor_add_one (5 * p 1 / 3)
  unfold brickRow
  constructor <;> linarith

theorem brickCol_bounds (p : Plane) :
    4 * (brickCol p : ℝ) / 5 + 8 * (brickRow p : ℝ) / 25 ≤ p 0 ∧
      p 0 < 4 * (brickCol p : ℝ) / 5 + 8 * (brickRow p : ℝ) / 25 + 4 / 5 := by
  have h1 := Int.floor_le (5 * p 0 / 4 - 2 * (brickRow p : ℝ) / 5)
  have h2 := Int.lt_floor_add_one (5 * p 0 / 4 - 2 * (brickRow p : ℝ) / 5)
  unfold brickCol
  constructor <;> linarith

theorem dist_sq_eq (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Same color forces the brick offsets `(di, dj)` into five cases. -/
theorem brick_cases (x y : Plane) (hc : brickColor x = brickColor y)
    (hj : |brickRow x - brickRow y| ≤ 2) (hi : |brickCol x - brickCol y| ≤ 3) :
    (brickCol y = brickCol x ∧ brickRow y = brickRow x) ∨
    (brickCol y = brickCol x + 2 ∧ brickRow y = brickRow x + 1) ∨
    (brickCol y = brickCol x - 2 ∧ brickRow y = brickRow x - 1) ∨
    (brickCol y = brickCol x - 3 ∧ brickRow y = brickRow x + 2) ∨
    (brickCol y = brickCol x + 3 ∧ brickRow y = brickRow x - 2) := by
  unfold brickColor at hc
  rw [Fin.mk.injEq] at hc
  rw [abs_le] at hj hi
  have hmod : (brickCol y - brickCol x + 5 * (brickRow y - brickRow x)) % 7 = 0 := by omega
  obtain ⟨d1, hd1⟩ : ∃ d, brickCol y = brickCol x + d := ⟨_, (add_sub_cancel _ _).symm⟩
  obtain ⟨d2, hd2⟩ : ∃ d, brickRow y = brickRow x + d := ⟨_, (add_sub_cancel _ _).symm⟩
  rw [hd1, hd2] at hmod ⊢
  rw [hd1] at hi
  rw [hd2] at hj
  have h1 : -3 ≤ d1 := by omega
  have h2 : d1 ≤ 3 := by omega
  have h3 : -2 ≤ d2 := by omega
  have h4 : d2 ≤ 2 := by omega
  interval_cases d1 <;> interval_cases d2 <;> omega

/-- **Main result.** Seven colors suffice. -/
theorem properColoring_seven : ProperColoring 7 := by
  refine ⟨brickColor, fun x y hxy hc => ?_⟩
  have hd : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 1 := by
    rw [← dist_sq_eq, hxy, one_pow]
  obtain ⟨rx1, rx2⟩ := brickRow_bounds x
  obtain ⟨ry1, ry2⟩ := brickRow_bounds y
  obtain ⟨cx1, cx2⟩ := brickCol_bounds x
  obtain ⟨cy1, cy2⟩ := brickCol_bounds y
  have hu1 : -1 ≤ x 0 - y 0 := by nlinarith [sq_nonneg (x 1 - y 1), sq_nonneg (x 0 - y 0 + 1)]
  have hu2 : x 0 - y 0 ≤ 1 := by nlinarith [sq_nonneg (x 1 - y 1), sq_nonneg (x 0 - y 0 - 1)]
  have hv1 : -1 ≤ x 1 - y 1 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1 + 1)]
  have hv2 : x 1 - y 1 ≤ 1 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1 - 1)]
  -- the rows differ by at most 2
  have hj : |brickRow x - brickRow y| ≤ 2 := by
    have a : ((brickRow x - brickRow y : ℤ) : ℝ) < 3 := by push_cast; linarith
    have b : (-3 : ℝ) < ((brickRow x - brickRow y : ℤ) : ℝ) := by push_cast; linarith
    have a' : brickRow x - brickRow y < 3 := by exact_mod_cast a
    have b' : -3 < brickRow x - brickRow y := by exact_mod_cast b
    rw [abs_le]
    constructor <;> omega
  have hjr : (-2 : ℝ) ≤ (brickRow x : ℝ) - brickRow y ∧ (brickRow x : ℝ) - brickRow y ≤ 2 := by
    rw [abs_le] at hj
    constructor
    · have : ((-2 : ℤ) : ℝ) ≤ ((brickRow x - brickRow y : ℤ) : ℝ) := Int.cast_le.mpr hj.1
      push_cast at this; linarith
    · have : ((brickRow x - brickRow y : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := Int.cast_le.mpr hj.2
      push_cast at this; linarith
  -- the bricks in a row differ by at most 3
  have hi : |brickCol x - brickCol y| ≤ 3 := by
    have a : ((brickCol x - brickCol y : ℤ) : ℝ) < 4 := by push_cast; linarith
    have b : (-4 : ℝ) < ((brickCol x - brickCol y : ℤ) : ℝ) := by push_cast; linarith
    have a' : brickCol x - brickCol y < 4 := by exact_mod_cast a
    have b' : -4 < brickCol x - brickCol y := by exact_mod_cast b
    rw [abs_le]
    constructor <;> omega
  rcases brick_cases x y hc hj hi with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  -- same brick: distance below the diagonal
  all_goals
    have f1 := congrArg (fun n : ℤ => (n : ℝ)) e1
    have f2 := congrArg (fun n : ℤ => (n : ℝ)) e2
    push_cast at f1 f2
    rw [f1, f2] at cy1 cy2
    rw [f2] at ry1 ry2
  · have a1 : x 0 - y 0 < 4 / 5 := by linarith
    have a2 : -(4 / 5) < x 0 - y 0 := by linarith
    have b1 : x 1 - y 1 < 3 / 5 := by linarith
    have b2 : -(3 / 5) < x 1 - y 1 := by linarith
    nlinarith [mul_pos (sub_pos.2 a1) (neg_lt_iff_pos_add.mp a2),
      mul_pos (sub_pos.2 b1) (neg_lt_iff_pos_add.mp b2)]
  · have a1 : x 0 - y 0 < -(28 / 25) := by linarith
    nlinarith [sq_nonneg (x 1 - y 1)]
  · have a1 : 28 / 25 < x 0 - y 0 := by linarith
    nlinarith [sq_nonneg (x 1 - y 1)]
  · have a1 : 24 / 25 < x 0 - y 0 := by linarith
    have b1 : x 1 - y 1 < -(3 / 5) := by linarith
    nlinarith
  · have a1 : x 0 - y 0 < -(24 / 25) := by linarith
    have b1 : 3 / 5 < x 1 - y 1 := by linarith
    nlinarith

end Portfolio.PlaneColoring

end

end
