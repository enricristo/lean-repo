/-
Copyright (c) 2026 Enrico Ambrosio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Ambrosio
-/
module

public import Portfolio

/-!
# Axiom audit

`#print axioms` lists every axiom a theorem depends on, following all the lemmas it uses.
The three below are the standard ones behind classical mathematics in Lean
(propositional extensionality, the axiom of choice, quotient soundness).
`#guard_msgs` fixes the expected output: if any step were left as `sorry`, the list would
gain `sorryAx` and the build would fail.
-/

/--
info: 'Portfolio.sub_sq_div_two_le_log_one_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.sub_sq_div_two_le_log_one_add

/--
info: 'Portfolio.tsum_telescopingTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.tsum_telescopingTerm

/--
info: 'Portfolio.piIntegral_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.piIntegral_two

/--
info: 'Portfolio.piP_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.piP_two

/--
info: 'Portfolio.piIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.piIntegral_eq

/--
info: 'Portfolio.piP_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.piP_eq

/--
info: 'Portfolio.dirac_not_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.dirac_not_regular

/--
info: 'Portfolio.dirac_not_regular_euclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.dirac_not_regular_euclidean

/--
info: 'Portfolio.hilgerExp_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.hilgerExp_unique

/--
info: 'Portfolio.eq_hilgerExp_of_deltaDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.eq_hilgerExp_of_deltaDeriv

/--
info: 'Portfolio.deltaDeriv_int' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.deltaDeriv_int

/--
info: 'Portfolio.tendsto_hilgerExp_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.tendsto_hilgerExp_exp

/--
info: 'Portfolio.hZ_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.hZ_induction

/--
info: 'Portfolio.ekeland' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.ekeland

/--
info: 'Portfolio.exists_almost_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.exists_almost_critical

/--
info: 'Portfolio.exists_critical_point_of_palaisSmale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Portfolio.exists_critical_point_of_palaisSmale
