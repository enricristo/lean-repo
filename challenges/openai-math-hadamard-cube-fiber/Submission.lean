import Mathlib

namespace OAI

/-! Cancellation of row ratios on a prescribed cubic fibre. -/

open scoped BigOperators Matrix

namespace HadamardSix

abbrev Index := Fin 6
abbrev Matrix6 := Matrix Index Index ℂ

def Unimodular (H : Matrix6) : Prop := ∀ i j, ‖H i j‖ = 1

def IsComplexHadamard (H : Matrix6) : Prop :=
  Unimodular H ∧ H.conjTranspose * H = (6 : ℂ) • (1 : Matrix6)

def entrywiseSquare (H : Matrix6) : Matrix6 := fun i j => H i j ^ 2

noncomputable def cubeFiber (v : Index → ℂ) (z : ℂ) : Finset Index := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = z)

noncomputable def rowRatio (H : Matrix6) (i j : Index) : Index → ℂ :=
  fun k => H i k * star (H j k)

/-! ## Proof

Write `r k` for the row ratio `H i k * star (H j k)`. It is unimodular, so `r² = r³ · star r`.
Orthogonality of rows `i` and `j` of `H` gives `∑ r = 0`; of `entrywiseSquare H`, `∑ r² = 0`.
On the fiber `S` where `r³ = a`, and on its complement where `r³ = b`, the second sum is
`a · star A + b · star B` with `A`, `B` the partial sums of `r`. With `A + B = 0` this gives
`(a - b) · star A = 0`, so `A = 0`. -/

/-- Rows of a complex Hadamard matrix are orthogonal. -/
theorem row_orthogonal {H : Matrix6} (hH : IsComplexHadamard H) {i j : Index} (hij : i ≠ j) :
    ∑ k, H i k * star (H j k) = 0 := by
  have h1 : (((6 : ℂ)⁻¹) • H.conjTranspose) * H = 1 := by
    rw [Matrix.smul_mul, hH.2, smul_smul]
    norm_num
  have h2 : H * (((6 : ℂ)⁻¹) • H.conjTranspose) = 1 := mul_eq_one_comm.mp h1
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.one_apply_ne hij, Matrix.mul_apply] at h3
  simp only [Matrix.conjTranspose_apply, smul_eq_mul] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · norm_num at h
  · exact h

theorem rowRatio_norm {H : Matrix6} (hH : IsComplexHadamard H) (i j k : Index) :
    ‖rowRatio H i j k‖ = 1 := by
  simp [rowRatio, hH.1 i k, hH.1 j k]

theorem mul_star_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  have h := Complex.mul_conj z
  rw [Complex.normSq_eq_norm_sq, hz] at h
  simpa using h

theorem sq_eq_cube_mul_star {z : ℂ} (hz : ‖z‖ = 1) : z ^ 2 = z ^ 3 * star z := by
  have h := mul_star_self_of_norm_one hz
  calc z ^ 2 = z ^ 2 * (z * star z) := by rw [h, mul_one]
    _ = z ^ 3 * star z := by ring

theorem sum_rowRatio {H : Matrix6} (hH : IsComplexHadamard H) {i j : Index} (hij : i ≠ j) :
    ∑ k, rowRatio H i j k = 0 :=
  row_orthogonal hH hij

theorem sum_rowRatio_sq {H : Matrix6} (hs : IsComplexHadamard (entrywiseSquare H))
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k ^ 2 = 0 := by
  have h := row_orthogonal hs hij
  simp only [entrywiseSquare, star_pow] at h
  simpa [rowRatio, mul_pow] using h

lemma rowRatio_cubeFiber_sum_zero {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j)
    (a b : ℂ) (hne : a ≠ b)
    (hab : ∀ k, rowRatio H i j k ^ 3 = a ∨ rowRatio H i j k ^ 3 = b) :
    ∑ k ∈ cubeFiber (rowRatio H i j) a, H i k * star (H j k) = 0 := by
  classical
  set r := rowRatio H i j with hr
  set S := cubeFiber r a with hS
  have memS : ∀ k, k ∈ S ↔ r k ^ 3 = a := fun k => by
    simp [hS, cubeFiber]
  have hsub : S ⊆ Finset.univ := Finset.subset_univ S
  -- the two partial sums of r
  set A := ∑ k ∈ S, r k with hA
  set B := ∑ k ∈ Finset.univ \ S, r k with hB
  have hAB : B + A = 0 := by
    rw [hA, hB, Finset.sum_sdiff hsub]
    exact sum_rowRatio hH hij
  -- the two partial sums of r²
  have hSq : ∑ k ∈ S, r k ^ 2 = a * star A := by
    rw [hA, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [sq_eq_cube_mul_star (rowRatio_norm hH i j k), (memS k).mp hk]
  have hSqc : ∑ k ∈ Finset.univ \ S, r k ^ 2 = b * star B := by
    rw [hB, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : r k ^ 3 = b := by
      rcases hab k with h | h
      · exact absurd ((memS k).mpr h) (Finset.mem_sdiff.mp hk).2
      · exact h
    rw [sq_eq_cube_mul_star (rowRatio_norm hH i j k), hk']
  have hsq : b * star B + a * star A = 0 := by
    rw [← hSq, ← hSqc, Finset.sum_sdiff hsub]
    exact sum_rowRatio_sq hs hij
  have hBA : B = -A := by linear_combination hAB
  have hstar : star B = -star A := by rw [hBA, star_neg]
  rw [hstar] at hsq
  have hzero : (a - b) * star A = 0 := by linear_combination hsq
  have hA0 : star A = 0 := (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  have : A = 0 := by simpa using congrArg star hA0
  simpa [hA, hr, rowRatio] using this

end HadamardSix

end OAI
