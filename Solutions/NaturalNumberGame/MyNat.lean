/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Mathlib

/-!
# The natural numbers of the Natural Number Game

A small copy of the setup of the Natural Number Game, so that my solutions compile here
exactly as I typed them in the game.

* `MyNat` has two constructors, `zero` and `succ`. Numerals `0, 1, 2, …` are notation for
  `zero, succ zero, succ (succ zero), …`.
* Addition is defined by recursion on the second argument, and the game gives exactly two facts
  about it: `add_zero` and `add_succ`.
* `one_eq_succ_zero`, `two_eq_succ_one`, `three_eq_succ_two`, `four_eq_succ_three` say how the
  first numerals unfold.
* In the game `rw` rewrites and stops: it does not try to close the goal with `rfl`. The
  macro below gives `rw` that behaviour inside the namespace `NNG`, so a proof that needs a final
  `rfl` in the game needs it here too.
-/

@[expose] public section

namespace NNG

/-- The game's `rw`: rewrite only, never close the goal with `rfl`. Active only where the
namespace `NNG` is open. -/
scoped macro_rules
  | `(tactic| rw $s:rwRuleSeq) => `(tactic| rewrite $s:rwRuleSeq)
  | `(tactic| rw $s:rwRuleSeq $loc:location) => `(tactic| rewrite $s:rwRuleSeq $loc:location)

/-- The natural numbers of the game: zero and successor. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving DecidableEq

namespace MyNat

/-- The numeral `n` as a `MyNat`. -/
def ofNat : ℕ → MyNat
  | 0 => zero
  | n + 1 => succ (ofNat n)

instance (n : ℕ) : OfNat MyNat n := ⟨ofNat n⟩

/-- Addition, by recursion on the second argument. -/
def add : MyNat → MyNat → MyNat
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add MyNat := ⟨add⟩

theorem zero_eq_0 : zero = 0 := rfl

/-- First axiom of addition. -/
theorem add_zero (a : MyNat) : a + 0 = a := rfl

/-- Second axiom of addition. -/
theorem add_succ (a d : MyNat) : a + succ d = succ (a + d) := rfl

theorem one_eq_succ_zero : (1 : MyNat) = succ 0 := rfl
theorem two_eq_succ_one : (2 : MyNat) = succ 1 := rfl
theorem three_eq_succ_two : (3 : MyNat) = succ 2 := rfl
theorem four_eq_succ_three : (4 : MyNat) = succ 3 := rfl

end MyNat

end NNG

end
