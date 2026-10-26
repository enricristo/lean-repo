import Mathlib

namespace OAI

/-! Existence of the fixed-length forced free energy of honeycomb walks. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

structure Vertex where
  col : ℤ
  row : ℤ
  up : Bool
  deriving DecidableEq

def up (i j : ℤ) : Vertex := ⟨i, j, true⟩

def down (i j : ℤ) : Vertex := ⟨i, j, false⟩

def rowSpacing : ℝ := Real.sqrt 3 / 2

def position (v : Vertex) : ℂ :=
  if v.up then
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1/2,
      rowSpacing * ((v.row : ℝ) + 1/3)⟩
  else
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1,
      rowSpacing * ((v.row : ℝ) + 2/3)⟩

def rho : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def neighbors (v : Vertex) : Finset Vertex :=
  if v.up then
    {down v.col (v.row-1), down v.col v.row, down (v.col-1) v.row}
  else
    {up v.col (v.row+1), up v.col v.row, up (v.col+1) v.row}

def walkLists (o : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[o]}
  | n+1 => (neighbors o).biUnion (fun v => (walkLists v n).image (List.cons o))

def saws (o : Vertex) (n : ℕ) : Finset (List Vertex) :=
  (walkLists o n).filter List.Nodup

def endpoint (o : Vertex) (γ : List Vertex) : Vertex := γ.getLastD o

def displacement (o : Vertex) (γ : List Vertex) : ℂ :=
  position (endpoint o γ) - position o

def projection (e z : ℂ) : ℝ := (star e * z).re

def partition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ γ ∈ saws o n, rho ^ n * Real.exp (s * projection e (displacement o γ))

def logPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.log (partition o e s n) / (n : ℝ)

def freeEnergy (o : Vertex) (e : ℂ) (s : ℝ) : ℝ :=
  Filter.limUnder atTop (logPartition o e s)
lemma hc_cons_of_mem {o : Vertex} {n : ℕ} {γ : List Vertex} (h : γ ∈ walkLists o n) :
    γ = o :: γ.tail := by
  induction n generalizing o γ with
  | zero => simp [walkLists] at h; subst h; rfl
  | succ n ih =>
    simp only [walkLists, Finset.mem_biUnion, Finset.mem_image] at h
    obtain ⟨v, -, δ, -, rfl⟩ := h
    rfl

lemma hc_endpoint_append (o : Vertex) (γ t : List Vertex) :
    endpoint o (γ ++ t) = t.getLastD (endpoint o γ) := by
  induction γ generalizing o with
  | nil => rfl
  | cons a l ih =>
    simp only [endpoint, List.cons_append, List.getLastD_cons] at ih ⊢
    exact ih a

lemma hc_endpoint_mem {o : Vertex} {n : ℕ} {γ : List Vertex} (h : γ ∈ walkLists o n) :
    endpoint o γ ∈ γ := by
  rw [hc_cons_of_mem h]
  simp only [endpoint, List.getLastD_cons]
  exact List.getLastD_mem_cons

lemma hc_endpoint_cons (v : Vertex) (t : List Vertex) :
    endpoint v (v :: t) = t.getLastD v := by
  simp only [endpoint, List.getLastD_cons]

lemma hc_split (n m : ℕ) : ∀ (o : Vertex) (γ : List Vertex), γ ∈ walkLists o (n + m) →
    ∃ γ1 ∈ walkLists o n, ∃ γ2 ∈ walkLists (endpoint o γ1) m, γ = γ1 ++ γ2.tail := by
  induction n with
  | zero =>
    intro o γ h
    refine ⟨[o], by simp [walkLists], γ, by simpa [endpoint] using h, ?_⟩
    rw [zero_add] at h
    conv_lhs => rw [hc_cons_of_mem h]
    rfl
  | succ n ih =>
    intro o γ h
    rw [Nat.add_right_comm] at h
    simp only [walkLists, Finset.mem_biUnion, Finset.mem_image] at h
    obtain ⟨v, hv, δ, hδ, rfl⟩ := h
    obtain ⟨δ1, h1, δ2, h2, rfl⟩ := ih v δ hδ
    refine ⟨o :: δ1, ?_, δ2, ?_, rfl⟩
    · simp only [walkLists, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨v, hv, δ1, h1, rfl⟩
    · have : endpoint o (o :: δ1) = endpoint v δ1 := by
        rw [hc_cons_of_mem h1]
        simp only [endpoint, List.getLastD_cons]
      rw [this]; exact h2

lemma hc_proj_add (e z w : ℂ) : projection e (z + w) = projection e z + projection e w := by
  simp [projection, mul_add]

lemma hc_rho_pos : 0 < rho := by
  unfold rho; positivity

lemma hc_saws_split {o : Vertex} {n m : ℕ} {γ : List Vertex} (h : γ ∈ saws o (n + m)) :
    ∃ γ1 ∈ saws o n, ∃ γ2 ∈ saws (endpoint o γ1) m, γ = γ1 ++ γ2.tail := by
  simp only [saws, Finset.mem_filter] at h ⊢
  obtain ⟨hw, hnd⟩ := h
  obtain ⟨γ1, h1, γ2, h2, rfl⟩ := hc_split n m o γ hw
  rw [List.nodup_append] at hnd
  obtain ⟨n1, n2, hdis⟩ := hnd
  refine ⟨γ1, ⟨h1, n1⟩, γ2, ⟨h2, ?_⟩, rfl⟩
  rw [hc_cons_of_mem h2, List.nodup_cons]
  exact ⟨fun hm => hdis _ (hc_endpoint_mem h1) _ hm rfl, n2⟩

lemma hc_term_split (o : Vertex) (e : ℂ) (s : ℝ) (γ1 t : List Vertex) (n m : ℕ) :
    rho ^ (n + m) * Real.exp (s * projection e (displacement o (γ1 ++ t))) =
    (rho ^ n * Real.exp (s * projection e (displacement o γ1))) *
    (rho ^ m * Real.exp (s * projection e
      (displacement (endpoint o γ1) (endpoint o γ1 :: t)))) := by
  have hd : displacement o (γ1 ++ t) =
      displacement (endpoint o γ1) (endpoint o γ1 :: t) + displacement o γ1 := by
    simp only [displacement, hc_endpoint_append, hc_endpoint_cons]
    ring
  rw [hd, hc_proj_add, mul_add, Real.exp_add, pow_add]
  ring

lemma hc_partition_add_le (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) :
    partition o e s (n + m) ≤ ∑ γ1 ∈ saws o n,
      (rho ^ n * Real.exp (s * projection e (displacement o γ1))) *
        partition (endpoint o γ1) e s m := by
  classical
  have hρ : 0 ≤ rho := hc_rho_pos.le
  set S := (saws o n).sigma (fun γ1 => saws (endpoint o γ1) m) with hS
  let ψ : (Σ _ : List Vertex, List Vertex) → List Vertex := fun p => p.1 ++ p.2.tail
  have hsub : saws o (n + m) ⊆ S.image ψ := by
    intro γ hγ
    obtain ⟨γ1, h1, γ2, h2, rfl⟩ := hc_saws_split hγ
    exact Finset.mem_image.mpr ⟨⟨γ1, γ2⟩, Finset.mem_sigma.mpr ⟨h1, h2⟩, rfl⟩
  unfold partition
  calc _ ≤ ∑ γ ∈ S.image ψ, rho ^ (n+m) * Real.exp (s * projection e (displacement o γ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => mul_nonneg (pow_nonneg hρ _) (Real.exp_pos _).le)
    _ ≤ ∑ p ∈ S, rho ^ (n+m) * Real.exp (s * projection e (displacement o (ψ p))) :=
        Finset.sum_image_le_of_nonneg
          (fun _ _ => mul_nonneg (pow_nonneg hρ _) (Real.exp_pos _).le)
    _ = ∑ γ1 ∈ saws o n, ∑ γ2 ∈ saws (endpoint o γ1) m,
          rho ^ (n+m) * Real.exp (s * projection e (displacement o (γ1 ++ γ2.tail))) :=
        Finset.sum_sigma _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl (fun γ1 _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun γ2 h2 => ?_)
        have h2' := hc_cons_of_mem (Finset.mem_filter.mp h2).1
        conv_rhs => rw [h2']
        exact hc_term_split o e s γ1 γ2.tail n m

lemma hc_partition_add_le' (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) (K : ℝ)
    (hK : ∀ γ1 ∈ saws o n, partition (endpoint o γ1) e s m ≤ K) :
    partition o e s (n + m) ≤ partition o e s n * K := by
  refine (hc_partition_add_le o e s n m).trans ?_
  unfold partition
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun γ1 h1 => ?_)
  exact mul_le_mul_of_nonneg_left (hK γ1 h1)
    (mul_nonneg (pow_nonneg hc_rho_pos.le _) (Real.exp_pos _).le)

lemma hc_shift_neighbors (a b : ℤ) (v : Vertex) :
    neighbors ⟨v.col + a, v.row + b, v.up⟩ =
      (neighbors v).image (fun w => ⟨w.col + a, w.row + b, w.up⟩) := by
  rcases v with ⟨i, j, u⟩
  cases u <;> simp only [neighbors, up, down, Finset.image_insert, Finset.image_singleton,
    Bool.false_eq_true, ite_false, ite_true] <;> ring_nf

lemma hc_shift_walkLists (a b : ℤ) (n : ℕ) : ∀ o : Vertex,
    walkLists ⟨o.col + a, o.row + b, o.up⟩ n =
      (walkLists o n).image
        (List.map (fun w : Vertex => (⟨w.col + a, w.row + b, w.up⟩ : Vertex))) := by
  induction n with
  | zero => intro o; simp [walkLists]
  | succ n ih =>
    intro o
    simp only [walkLists]
    rw [hc_shift_neighbors, Finset.image_biUnion, Finset.biUnion_image]
    refine Finset.biUnion_congr rfl (fun v _ => ?_)
    rw [ih v, Finset.image_image, Finset.image_image]
    rfl

lemma hc_position_shift (a b : ℤ) (v : Vertex) :
    position ⟨v.col + a, v.row + b, v.up⟩ =
      position v + ⟨(a : ℝ) + (b : ℝ) / 2, rowSpacing * b⟩ := by
  rcases v with ⟨i, j, u⟩
  cases u <;> apply Complex.ext <;> simp [position] <;> ring

lemma hc_partition_shift (a b : ℤ) (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition ⟨o.col + a, o.row + b, o.up⟩ e s n = partition o e s n := by
  classical
  set T : Vertex → Vertex := fun w => ⟨w.col + a, w.row + b, w.up⟩ with hT
  have hTi : Function.Injective T := by
    intro x y h
    rcases x with ⟨x1, x2, x3⟩
    rcases y with ⟨y1, y2, y3⟩
    simp only [hT, Vertex.mk.injEq, add_left_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  unfold partition saws
  rw [hc_shift_walkLists, Finset.filter_image, Finset.sum_image]
  · rw [Finset.filter_congr (fun γ _ => List.nodup_map_iff hTi)]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    have hend : endpoint ⟨o.col + a, o.row + b, o.up⟩ (List.map T γ) = T (endpoint o γ) :=
      List.getLastD_map
    simp only [displacement]
    rw [hend]
    simp only [hT, hc_position_shift]
    ring_nf
  · intro x _ y _ h
    exact (List.map_injective_iff.mpr hTi) h

lemma hc_partition_base (v : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition v e s n = partition ⟨0, 0, v.up⟩ e s n := by
  have h := hc_partition_shift v.col v.row ⟨0, 0, v.up⟩ e s n
  simp only [zero_add] at h
  exact h

lemma hc_exists_saw (n : ℕ) : ∀ o : Vertex, ∃ γ ∈ walkLists o n, γ.Nodup ∧
    ∀ w ∈ γ, 2 * o.col + (if o.up then 0 else 1) ≤ 2 * w.col + (if w.up then 0 else 1) := by
  induction n with
  | zero => intro o; exact ⟨[o], by simp [walkLists], List.nodup_singleton o, by simp⟩
  | succ n ih =>
    intro o
    obtain ⟨v, hv, hφ⟩ : ∃ v ∈ neighbors o,
        2 * v.col + (if v.up then 0 else 1) = 2 * o.col + (if o.up then 0 else 1) + 1 := by
      rcases o with ⟨i, j, u⟩
      cases u
      · exact ⟨⟨i + 1, j, true⟩, by simp [neighbors, up], by simp; ring⟩
      · exact ⟨⟨i, j, false⟩, by simp [neighbors, down], by simp⟩
    obtain ⟨δ, hδ, hnd, hmono⟩ := ih v
    refine ⟨o :: δ, ?_, ?_, ?_⟩
    · simp only [walkLists, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨v, hv, δ, hδ, rfl⟩
    · rw [List.nodup_cons]
      refine ⟨fun ho => ?_, hnd⟩
      have := hmono o ho
      omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact le_rfl
      · have := hmono w hw; omega

lemma hc_partition_pos (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : 0 < partition o e s n := by
  obtain ⟨γ, hγ, hnd, -⟩ := hc_exists_saw n o
  unfold partition
  exact Finset.sum_pos (fun _ _ => mul_pos (pow_pos hc_rho_pos _) (Real.exp_pos _))
    ⟨γ, Finset.mem_filter.mpr ⟨hγ, hnd⟩⟩

lemma hc_step_bound {o v : Vertex} (hv : v ∈ neighbors o) : ‖position v - position o‖ ≤ 2 := by
  have hr0 : 0 ≤ rowSpacing := by unfold rowSpacing; positivity
  have hr1 : rowSpacing ≤ 1 := by
    unfold rowSpacing
    have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have h0 := Real.sqrt_nonneg 3
    nlinarith
  have key : -1 ≤ (position v - position o).re ∧ (position v - position o).re ≤ 1 ∧
      -1 ≤ (position v - position o).im ∧ (position v - position o).im ≤ 1 := by
    rcases o with ⟨i, j, u⟩
    cases u <;> simp [neighbors, up, down] at hv <;> rcases hv with rfl | rfl | rfl <;>
      simp [position] <;> and_intros <;> linarith
  obtain ⟨a1, a2, a3, a4⟩ := key
  have b1 := abs_le.mpr ⟨a1, a2⟩
  have b2 := abs_le.mpr ⟨a3, a4⟩
  have := Complex.norm_le_abs_re_add_abs_im (position v - position o)
  linarith

lemma hc_disp_bound (n : ℕ) : ∀ (o : Vertex) (γ : List Vertex), γ ∈ walkLists o n →
    ‖position (endpoint o γ) - position o‖ ≤ 2 * n := by
  induction n with
  | zero =>
    intro o γ h
    simp [walkLists] at h; subst h
    simp [endpoint]
  | succ n ih =>
    intro o γ h
    simp only [walkLists, Finset.mem_biUnion, Finset.mem_image] at h
    obtain ⟨v, hv, δ, hδ, rfl⟩ := h
    have hend : endpoint o (o :: δ) = endpoint v δ := by
      rw [hc_cons_of_mem hδ]
      simp only [endpoint, List.getLastD_cons]
    rw [hend]
    refine (norm_sub_le_norm_sub_add_norm_sub _ (position v) _).trans ?_
    have := ih v δ hδ
    have := hc_step_bound hv
    push_cast
    linarith

lemma hc_le_M (v : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition v e s n ≤ max (partition (up 0 0) e s n) (partition (down 0 0) e s n) := by
  rw [hc_partition_base]
  rcases v with ⟨i, j, u⟩
  cases u
  · exact le_max_right _ _
  · exact le_max_left _ _

lemma hc_M_submul (e : ℂ) (s : ℝ) (n m : ℕ) :
    max (partition (up 0 0) e s (n + m)) (partition (down 0 0) e s (n + m)) ≤
      max (partition (up 0 0) e s n) (partition (down 0 0) e s n) *
        max (partition (up 0 0) e s m) (partition (down 0 0) e s m) := by
  have hM : 0 ≤ max (partition (up 0 0) e s m) (partition (down 0 0) e s m) :=
    (hc_partition_pos _ e s m).le.trans (le_max_left _ _)
  apply max_le
  · refine (hc_partition_add_le' (up 0 0) e s n m _ (fun γ1 _ => hc_le_M _ e s m)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  · refine (hc_partition_add_le' (down 0 0) e s n m _ (fun γ1 _ => hc_le_M _ e s m)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hM

lemma hc_neighbor_up {w v : Vertex} (hv : v ∈ neighbors w) : v.up = !w.up := by
  rcases w with ⟨i, j, u⟩
  cases u <;> simp [neighbors, up, down] at hv <;> rcases hv with rfl | rfl | rfl <;> rfl

lemma hc_endpoint_one {w : Vertex} {l : List Vertex} (h : l ∈ walkLists w 1) :
    endpoint w l ∈ neighbors w := by
  simp only [walkLists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_singleton] at h
  obtain ⟨v, hv, δ, rfl, rfl⟩ := h
  simpa [endpoint] using hv

lemma hc_flip (w o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) (ho : o.up = !w.up) :
    partition w e s (1 + n) ≤ partition w e s 1 * partition o e s n := by
  refine hc_partition_add_le' w e s 1 n _ (fun γ1 h1 => le_of_eq ?_)
  have hn := hc_endpoint_one (Finset.mem_filter.mp h1).1
  rw [hc_partition_base, hc_partition_base o, hc_neighbor_up hn, ho]

lemma hc_lower (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    max (partition (up 0 0) e s (n + 1)) (partition (down 0 0) e s (n + 1)) ≤
      max (partition (up 0 0) e s 1) (partition (down 0 0) e s 1) * partition o e s n := by
  have hp := (hc_partition_pos o e s n).le
  have A : partition ⟨0, 0, o.up⟩ e s (n + 1) ≤
      max (partition (up 0 0) e s 1) (partition (down 0 0) e s 1) * partition o e s n := by
    have := hc_partition_add_le' ⟨0, 0, o.up⟩ e s n 1 _ (fun γ1 _ => hc_le_M _ e s 1)
    rw [← hc_partition_base o e s n] at this
    linarith
  have B : partition ⟨0, 0, !o.up⟩ e s (n + 1) ≤
      max (partition (up 0 0) e s 1) (partition (down 0 0) e s 1) * partition o e s n := by
    rw [add_comm]
    refine (hc_flip ⟨0, 0, !o.up⟩ o e s n (by simp)).trans ?_
    exact mul_le_mul_of_nonneg_right (hc_le_M _ e s 1) hp
  rcases o with ⟨i, j, u⟩
  cases u
  · exact max_le B A
  · exact max_le A B

lemma hc_lower_bound (e : ℂ) (s : ℝ) (n : ℕ) :
    (n : ℝ) * (Real.log rho - 2 * |s| * ‖e‖) ≤
      Real.log (max (partition (up 0 0) e s n) (partition (down 0 0) e s n)) := by
  obtain ⟨γ, hγ, hnd, -⟩ := hc_exists_saw n (up 0 0)
  set z := displacement (up 0 0) γ with hz
  have hzb : ‖z‖ ≤ 2 * n := hc_disp_bound n _ γ hγ
  have hp : |projection e z| ≤ ‖e‖ * ‖z‖ := by
    unfold projection
    calc _ ≤ ‖star e * z‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_star]
  have hsp : -(|s| * ‖e‖ * (2 * n)) ≤ s * projection e z := by
    have h1 := neg_abs_le (s * projection e z)
    rw [abs_mul] at h1
    have h2 : |s| * |projection e z| ≤ |s| * (‖e‖ * (2 * n)) :=
      mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left hzb (norm_nonneg _)))
        (abs_nonneg _)
    linarith
  have hterm : rho ^ n * Real.exp (s * projection e z) ≤
      max (partition (up 0 0) e s n) (partition (down 0 0) e s n) := by
    refine le_trans ?_ (le_max_left _ _)
    unfold partition
    exact Finset.single_le_sum
      (f := fun γ => rho ^ n * Real.exp (s * projection e (displacement (up 0 0) γ)))
      (fun _ _ => mul_nonneg (pow_nonneg hc_rho_pos.le _) (Real.exp_pos _).le)
      (Finset.mem_filter.mpr ⟨hγ, hnd⟩)
  have hpos : 0 < rho ^ n * Real.exp (s * projection e z) :=
    mul_pos (pow_pos hc_rho_pos _) (Real.exp_pos _)
  have hlog := Real.log_le_log hpos hterm
  rw [Real.log_mul (pow_pos hc_rho_pos _).ne' (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp] at hlog
  nlinarith

theorem logPartition_tendsto (o : Vertex) (e : ℂ) (s : ℝ) :
    Tendsto (logPartition o e s) atTop (𝓝 (freeEnergy o e s)) := by
  set M : ℕ → ℝ := fun n => max (partition (up 0 0) e s n) (partition (down 0 0) e s n)
    with hMdef
  have hMpos : ∀ n, 0 < M n := fun n => lt_max_of_lt_left (hc_partition_pos _ _ _ _)
  set u : ℕ → ℝ := fun n => Real.log (M n) with hudef
  have hsub : Subadditive u := fun m n => by
    show Real.log (M (m + n)) ≤ Real.log (M m) + Real.log (M n)
    rw [← Real.log_mul (hMpos m).ne' (hMpos n).ne']
    exact Real.log_le_log (hMpos _) (hc_M_submul e s m n)
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨min 0 (Real.log rho - 2 * |s| * ‖e‖), ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have key := hc_lower_bound e s n
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine (min_le_right _ _).trans ?_
      rw [le_div_iff₀ hn']
      linarith
  have hT := hsub.tendsto_lim hbdd
  refine tendsto_nhds_limUnder ⟨hsub.lim, ?_⟩
  have hup : ∀ n, logPartition o e s n ≤ u n / n := fun n =>
    div_le_div_of_nonneg_right
      (Real.log_le_log (hc_partition_pos o e s n) (hc_le_M o e s n)) (Nat.cast_nonneg n)
  have hlow : ∀ n ≥ 1, (u (n + 1) - Real.log (M 1)) / n ≤ logPartition o e s n := by
    intro n _
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    have h1 := Real.log_le_log (hMpos (n + 1)) (hc_lower o e s n)
    rw [Real.log_mul (hMpos 1).ne' (hc_partition_pos o e s n).ne'] at h1
    show Real.log (M (n + 1)) - Real.log (M 1) ≤ Real.log (partition o e s n)
    linarith
  have A : Tendsto (fun n : ℕ => u (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 hsub.lim) :=
    hT.comp (tendsto_add_atTop_nat 1)
  have B : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  have C : Tendsto (fun n : ℕ => Real.log (M 1) * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (M 1))
  have D : Tendsto (fun n : ℕ => (u (n + 1) - Real.log (M 1)) / n) atTop (𝓝 hsub.lim) := by
    have := (A.mul B).sub C
    rw [mul_one, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact this.ne'
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hn1 ⊢
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' D hT
    (eventually_atTop.2 ⟨1, hlow⟩) (Eventually.of_forall hup)

end HoneycombForce

end

end OAI
