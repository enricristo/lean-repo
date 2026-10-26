import Mathlib

namespace OAI

noncomputable section
namespace TruffetV4Counterexample

abbrev Coeff := WithBot ℝ

abbrev Form := Fin 3 → Coeff

abbrev Var := Fin 2

abbrev RowIndex := Fin 2

def column (j : Var) : Fin 3 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def nullForm : Form := fun _ => ⊥

structure Row where
  lhs : Form
  rhs : Form

structure State where
  rows : RowIndex → Row
  cost : Form
  remaining : Var → Prop

def wellFormed (s : State) : Prop := ∀ j, ¬ s.remaining j →
  s.cost (column j) = ⊥ ∧ ∀ i,
    (s.rows i).lhs (column j) = ⊥ ∧ (s.rows i).rhs (column j) = ⊥

def eval (f : Form) (w : Fin 3 → ℝ) : Coeff :=
  max (f 0 + (w 0 : Coeff)) (max (f 1 + (w 1 : Coeff)) (f 2 + (w 2 : Coeff)))

def feasible (s : State) (w : Fin 3 → ℝ) : Prop :=
  ∀ i, eval (s.rows i).rhs w ≤ eval (s.rows i).lhs w

def lower (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).lhs (column j) ≠ ⊥ ∧
    (s.rows i).rhs (column j) < (s.rows i).lhs (column j)

def upper (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).rhs (column j) ≠ ⊥ ∧
    (s.rows i).lhs (column j) < (s.rows i).rhs (column j)

def dominating (s : State) (j : Var) : Prop :=
  s.remaining j ∧ (∃ i, lower s i j) ∧ ∃ i, upper s i j

def eligible (s : State) (i : RowIndex) (j : Var) : Prop :=
  s.remaining j ∧ lower s i j ∧ ((∃ k, dominating s k) → dominating s j)

def bounded (s : State) : Prop :=
  ∀ j, s.remaining j → (∃ i, lower s i j) ∨ ∃ i, upper s i j

def stop (s : State) : Prop := ∀ i, (s.rows i).rhs 2 ≤ (s.rows i).lhs 2

def switch (s : State) : Prop :=
  (∀ j, s.remaining j → s.cost (column j) = ⊥) ∧ ¬ stop s ∧
  (∃ j, s.remaining j) ∧
  (¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
  ∃ i j, s.remaining j ∧ upper s i j

def failure (s : State) : Prop := ¬ stop s ∧
  ((¬ ∃ j, s.remaining j) ∨
   ((¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
    (¬ ∃ i j, s.remaining j ∧ upper s i j)))

def lowerForm (s : State) (i : RowIndex) (j : Var) : Form := fun k =>
  if k = column j then ⊥ else
    (s.rows i).rhs k + ((-WithBot.unbotD 0 ((s.rows i).lhs (column j)) : ℝ) : Coeff)

def substitute (f : Form) (j : Var) (g : Form) : Form := fun k =>
  if k = column j then ⊥ else max (f k) (f (column j) + g k)

def cleanup (r : Row) : Row := by
  classical
  exact if ∀ k, r.rhs k ≤ r.lhs k then ⟨nullForm, nullForm⟩ else r

def advance (s : State) (i : RowIndex) (j : Var) : State where
  rows := fun r => cleanup ⟨substitute (s.rows r).lhs j (lowerForm s i j),
    substitute (s.rows r).rhs j (lowerForm s i j)⟩
  cost := substitute s.cost j (lowerForm s i j)
  remaining := fun k => s.remaining k ∧ k ≠ j

def ForcedSingletonStep (s s' : State) (i : RowIndex) (j : Var) : Prop :=
  wellFormed s ∧ wellFormed s' ∧
  bounded s ∧ ¬ stop s ∧ ¬ switch s ∧ ¬ failure s ∧
  (∀ r k, eligible s r k ↔ r = i ∧ k = j) ∧
  (∃ k, (substitute s.cost j (lowerForm s i j)) k ≠ ⊥) ∧
  s' = advance s i j

def initial : State where
  rows := ![⟨![(0 : Coeff), 0, ⊥], ![⊥, ⊥, (0 : Coeff)]⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, (1 : Coeff), ((-2 : ℝ) : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun _ => True

def middle : State where
  rows := ![⟨nullForm, nullForm⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, ⊥, (1 : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun j => j = 0

def finalState : State where
  rows := fun _ => ⟨nullForm, nullForm⟩
  cost := ![⊥, ⊥, (1 : Coeff)]
  remaining := fun _ => False

def crossRowRestriction (s : State) : Prop :=
  ∀ i r : RowIndex, i ≠ r → ∀ α : ℝ, ∃ w : Fin 3 → ℝ,
    eval (s.rows i).lhs w < (α : Coeff) + eval (s.rows r).rhs w

def output : Fin 3 → ℝ := ![1, 0, 0]

def better : Fin 3 → ℝ := ![0, -1, 0]

/-! ### Auxiliary lemmas -/

lemma c0 : (0 : Coeff) = ((0 : ℝ) : Coeff) := rfl
lemma c1 : (1 : Coeff) = ((1 : ℝ) : Coeff) := rfl

lemma cleanup_of_le (r : Row) (h : ∀ k, r.rhs k ≤ r.lhs k) :
    cleanup r = ⟨nullForm, nullForm⟩ := by
  unfold cleanup; exact ite_eq_left_iff.mpr (fun h' => absurd h h')

lemma cleanup_of_not (r : Row) (k : Fin 3) (h : ¬ r.rhs k ≤ r.lhs k) :
    cleanup r = r := by
  unfold cleanup; exact ite_eq_right_iff.mpr (fun h' => absurd (h' k) h)

lemma state_ext {s t : State} (h1 : s.rows = t.rows) (h2 : s.cost = t.cost)
    (h3 : s.remaining = t.remaining) : s = t := by
  cases s; cases t; cases h1; cases h2; cases h3; rfl

/-! ### Cross-row restriction -/

theorem cross_initial : crossRowRestriction initial := by
  intro i r hir α
  refine ⟨![0, 0, 3 - α], ?_⟩
  fin_cases i <;> fin_cases r <;> simp at hir <;>
  · simp [eval, initial]
    simp only [c0, c1, ← WithBot.coe_add, ← WithBot.coe_max, WithBot.coe_lt_coe]
    norm_num
    try linarith [le_max_right (1:ℝ) (-2 + (3 - α))]

/-! ### Well-formedness, boundedness, stop/switch/failure -/

theorem wellFormed_initial : wellFormed initial := by
  intro j hj
  exact absurd trivial hj

theorem wellFormed_middle : wellFormed middle := by
  intro j hj
  fin_cases j
  · exact absurd rfl hj
  · refine ⟨rfl, fun i => ?_⟩
    fin_cases i <;> exact ⟨rfl, rfl⟩

theorem wellFormed_finalState : wellFormed finalState := by
  intro j _
  refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
  fin_cases j <;> rfl

theorem lower_initial_0_0 : lower initial 0 0 := by
  simp [lower, initial, column]

theorem lower_initial_0_1 : lower initial 0 1 := by
  simp [lower, initial, column]

theorem lower_middle_1_0 : lower middle 1 0 := by
  simp [lower, middle, column]

theorem bounded_initial : bounded initial := by
  intro j _
  left
  fin_cases j
  · exact ⟨0, lower_initial_0_0⟩
  · exact ⟨0, lower_initial_0_1⟩

theorem bounded_middle : bounded middle := by
  intro j hj
  fin_cases j
  · exact Or.inl ⟨1, lower_middle_1_0⟩
  · exact absurd hj (by simp [middle])

theorem not_stop_initial : ¬ stop initial := by
  intro h
  have h0 := h 0
  simp [initial] at h0

theorem not_stop_middle : ¬ stop middle := by
  intro h
  have h1 := h 1
  simp [middle] at h1

theorem not_switch_initial : ¬ switch initial := by
  intro h
  have := h.1 0 trivial
  simp [initial, column] at this

theorem not_switch_middle : ¬ switch middle := by
  intro h
  have := h.1 0 rfl
  simp [middle, column] at this

theorem not_failure_initial : ¬ failure initial := by
  rintro ⟨_, h | ⟨h, _⟩⟩
  · exact h ⟨0, trivial⟩
  · exact h ⟨0, 0, trivial, lower_initial_0_0⟩

theorem not_failure_middle : ¬ failure middle := by
  rintro ⟨_, h | ⟨h, _⟩⟩
  · exact h ⟨0, rfl⟩
  · exact h ⟨1, 0, rfl, lower_middle_1_0⟩

/-! ### Eligibility -/

theorem eligible_initial : ∀ r k, eligible initial r k ↔ r = 0 ∧ k = 1 := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [eligible, dominating, lower, upper, initial, column, Fin.exists_fin_two]

theorem eligible_middle : ∀ r k, eligible middle r k ↔ r = 1 ∧ k = 0 := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [eligible, dominating, lower, upper, middle, column, Fin.exists_fin_two, nullForm]

/-! ### Nonempty substitutions -/

theorem subst_cost_initial : ∃ k, (substitute initial.cost 1 (lowerForm initial 0 1)) k ≠ ⊥ := by
  refine ⟨0, ?_⟩
  simp [substitute, lowerForm, initial, column]

theorem subst_cost_middle : ∃ k, (substitute middle.cost 0 (lowerForm middle 1 0)) k ≠ ⊥ := by
  refine ⟨2, ?_⟩
  simp [substitute, lowerForm, middle, column]

/-! ### The two state equalities -/

lemma advance_initial_row0 : (advance initial 0 1).rows 0 = ⟨nullForm, nullForm⟩ := by
  dsimp only [advance]
  rw [cleanup_of_le]
  intro k
  fin_cases k <;> simp [substitute, lowerForm, initial, column]

lemma advance_initial_row1 :
    (advance initial 0 1).rows 1 = ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, ⊥, (1 : Coeff)]⟩ := by
  dsimp only [advance]
  rw [cleanup_of_not _ 2 (by simp [substitute, lowerForm, initial, column])]
  simp only [Row.mk.injEq]
  constructor <;> funext k <;> fin_cases k <;>
    simp [substitute, lowerForm, initial, column]
  norm_num

theorem middle_eq_advance : middle = advance initial 0 1 := by
  apply state_ext
  · funext r
    fin_cases r
    · exact advance_initial_row0.symm
    · exact advance_initial_row1.symm
  · funext k
    fin_cases k <;> simp [advance, substitute, lowerForm, initial, middle, column]
  · funext k
    fin_cases k <;> simp [advance, initial, middle]

lemma advance_middle_row (r : RowIndex) :
    (advance middle 1 0).rows r = ⟨nullForm, nullForm⟩ := by
  dsimp only [advance]
  rw [cleanup_of_le]
  intro k
  fin_cases r <;> fin_cases k <;> simp [substitute, lowerForm, middle, column, nullForm]

theorem finalState_eq_advance : finalState = advance middle 1 0 := by
  apply state_ext
  · funext r
    exact (advance_middle_row r).symm
  · funext k
    fin_cases k <;> simp [advance, substitute, lowerForm, finalState, middle, column]
  · funext k
    fin_cases k <;> simp [advance, finalState, middle]

/-! ### The two forced singleton steps -/

theorem step_initial : ForcedSingletonStep initial middle 0 1 :=
  ⟨wellFormed_initial, wellFormed_middle, bounded_initial, not_stop_initial,
    not_switch_initial, not_failure_initial, eligible_initial, subst_cost_initial,
    middle_eq_advance⟩

theorem step_middle : ForcedSingletonStep middle finalState 1 0 :=
  ⟨wellFormed_middle, wellFormed_finalState, bounded_middle, not_stop_middle,
    not_switch_middle, not_failure_middle, eligible_middle, subst_cost_middle,
    finalState_eq_advance⟩

/-! ### Facts about the final state -/

theorem finalState_no_remaining : ¬ ∃ j, finalState.remaining j := fun ⟨_, h⟩ => h

theorem stop_finalState : stop finalState := fun _ => le_rfl

/-! ### Feasibility and evaluations -/

theorem feasible_output : feasible initial output := by
  intro i
  fin_cases i
  · simp [eval, initial, output]
  · simp [eval, initial, output]
    norm_num

theorem feasible_better : feasible initial better := by
  intro i
  fin_cases i
  · simp [eval, initial, better]
  · simp [eval, initial, better]
    simp only [c0, c1, ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_num

theorem eval_lowerForm_initial : (output 1 : Coeff) = eval (lowerForm initial 0 1) output := by
  simp [eval, lowerForm, initial, output, column]

theorem eval_lowerForm_middle : (output 0 : Coeff) = eval (lowerForm middle 1 0) output := by
  simp [eval, lowerForm, middle, output, column]

theorem eval_cost_eq : eval initial.cost output = eval finalState.cost output := by
  simp [eval, initial, finalState, output]

theorem eval_cost_lt : eval initial.cost better < eval finalState.cost output := by
  simp [eval, initial, finalState, output, better]

theorem finite_execution_not_optimal :
    crossRowRestriction initial ∧
    ForcedSingletonStep initial middle 0 1 ∧
    ForcedSingletonStep middle finalState 1 0 ∧
    (¬ ∃ j, finalState.remaining j) ∧ stop finalState ∧
    feasible initial output ∧ feasible initial better ∧
    output 2 = 0 ∧ better 2 = 0 ∧
    (output 1 : Coeff) = eval (lowerForm initial 0 1) output ∧
    (output 0 : Coeff) = eval (lowerForm middle 1 0) output ∧
    eval initial.cost output = eval finalState.cost output ∧
    eval initial.cost better < eval finalState.cost output := by
  exact ⟨cross_initial, step_initial, step_middle, finalState_no_remaining, stop_finalState,
    feasible_output, feasible_better, rfl, rfl, eval_lowerForm_initial,
    eval_lowerForm_middle, eval_cost_eq, eval_cost_lt⟩

end TruffetV4Counterexample
end

end OAI
