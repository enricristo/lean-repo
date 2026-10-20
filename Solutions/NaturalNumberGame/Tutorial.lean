/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Solutions.NaturalNumberGame.MyNat

/-!
# Natural Number Game: Tutorial World

My solutions to the Tutorial World of the Natural Number Game
(https://adam.math.hhu.de/#/g/leanprover-community/nng4). Statements are the game's,
proofs are mine, typed as I entered them in the game.

The proofs run on `MyNat`, the game's own natural numbers, rebuilt in
`Solutions/NaturalNumberGame/MyNat.lean`. One difference from plain Lean: in the game, `rw`
only rewrites and never closes a goal by itself, which is why the proofs end with `rfl`.
`MyNat.lean` defines `rw` the same way for these files.
-/

@[expose] public section

namespace NNG.Tutorial

open MyNat

/-- **Level 7.** The successor of `n` is `n + 1`. The proof unfolds `1` as `succ 0` and then
uses the two axioms of addition. -/
theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rfl

/-- **Level 8.** `2 + 2 = 4`. The proof writes every numeral in terms of `succ`, moves one
`succ` out of the sum with `add_succ`, and then turns each `succ` back into `+ 1` with
Level 7, until both sides read the same. -/
example : (2 : MyNat) + 2 = 4 := by
  rw [two_eq_succ_one]
  rw [four_eq_succ_three]
  rw [three_eq_succ_two]
  rw [two_eq_succ_one]
  rw [add_succ]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  rfl

end NNG.Tutorial

end
