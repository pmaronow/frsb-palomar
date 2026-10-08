module

public import FRSB.NumberedResults

@[expose] public section

/-! Exact type and axiom checks for all numbered paper statements. -/
example : FRSB.Numbered.Statement_1_1 := FRSB.Numbered.result_1_1
example : FRSB.Numbered.Statement_1_2 := FRSB.Numbered.result_1_2
example : FRSB.Numbered.Statement_2_1 := FRSB.Numbered.result_2_1
example : FRSB.Numbered.Statement_2_2 := FRSB.Numbered.result_2_2
example : FRSB.Numbered.Statement_2_3 := FRSB.Numbered.result_2_3
example : FRSB.Numbered.Statement_2_4 := FRSB.Numbered.result_2_4
example : FRSB.Numbered.Statement_2_5 := FRSB.Numbered.result_2_5
example : FRSB.Numbered.Statement_2_6 := FRSB.Numbered.result_2_6
example : FRSB.Numbered.Statement_2_7 := FRSB.Numbered.result_2_7
example : FRSB.Numbered.Statement_3_1 := FRSB.Numbered.result_3_1
example : FRSB.Numbered.Statement_3_2 := FRSB.Numbered.result_3_2
example : FRSB.Numbered.Statement_3_3 := FRSB.Numbered.result_3_3
example : FRSB.Numbered.Statement_3_4 := FRSB.Numbered.result_3_4
example : FRSB.Numbered.Statement_4_1 := FRSB.Numbered.result_4_1
example : FRSB.Numbered.Statement_4_2 := FRSB.Numbered.result_4_2
example : FRSB.Numbered.Statement_4_3 := FRSB.Numbered.result_4_3
example : FRSB.Numbered.Statement_5_1 := FRSB.Numbered.result_5_1
example : FRSB.Numbered.Statement_5_2 := FRSB.Numbered.result_5_2
example : FRSB.Numbered.Statement_5_3 := FRSB.Numbered.result_5_3
example : FRSB.Numbered.Statement_5_4 := FRSB.Numbered.result_5_4
example : FRSB.Numbered.Statement_5_5 := FRSB.Numbered.result_5_5
example : FRSB.Numbered.Statement_5_6 := FRSB.Numbered.result_5_6
example : FRSB.Numbered.Statement_6_1 := FRSB.Numbered.result_6_1
example : FRSB.Numbered.Statement_6_2 := FRSB.Numbered.result_6_2
example : FRSB.Numbered.Statement_6_3 := FRSB.Numbered.result_6_3
example : FRSB.Numbered.Statement_6_4 := FRSB.Numbered.result_6_4

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.Numbered.result_1_1,
    ``FRSB.Numbered.result_1_2,
    ``FRSB.Numbered.result_2_1,
    ``FRSB.Numbered.result_2_2,
    ``FRSB.Numbered.result_2_3,
    ``FRSB.Numbered.result_2_4,
    ``FRSB.Numbered.result_2_5,
    ``FRSB.Numbered.result_2_6,
    ``FRSB.Numbered.result_2_7,
    ``FRSB.Numbered.result_3_1,
    ``FRSB.Numbered.result_3_2,
    ``FRSB.Numbered.result_3_3,
    ``FRSB.Numbered.result_3_4,
    ``FRSB.Numbered.result_4_1,
    ``FRSB.Numbered.result_4_2,
    ``FRSB.Numbered.result_4_3,
    ``FRSB.Numbered.result_5_1,
    ``FRSB.Numbered.result_5_2,
    ``FRSB.Numbered.result_5_3,
    ``FRSB.Numbered.result_5_4,
    ``FRSB.Numbered.result_5_5,
    ``FRSB.Numbered.result_5_6,
    ``FRSB.Numbered.result_6_1,
    ``FRSB.Numbered.result_6_2,
    ``FRSB.Numbered.result_6_3,
    ``FRSB.Numbered.result_6_4] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.Numbered.result_1_1
#print axioms FRSB.Numbered.result_1_2
#print axioms FRSB.Numbered.result_2_1
#print axioms FRSB.Numbered.result_2_2
#print axioms FRSB.Numbered.result_2_3
#print axioms FRSB.Numbered.result_2_4
#print axioms FRSB.Numbered.result_2_5
#print axioms FRSB.Numbered.result_2_6
#print axioms FRSB.Numbered.result_2_7
#print axioms FRSB.Numbered.result_3_1
#print axioms FRSB.Numbered.result_3_2
#print axioms FRSB.Numbered.result_3_3
#print axioms FRSB.Numbered.result_3_4
#print axioms FRSB.Numbered.result_4_1
#print axioms FRSB.Numbered.result_4_2
#print axioms FRSB.Numbered.result_4_3
#print axioms FRSB.Numbered.result_5_1
#print axioms FRSB.Numbered.result_5_2
#print axioms FRSB.Numbered.result_5_3
#print axioms FRSB.Numbered.result_5_4
#print axioms FRSB.Numbered.result_5_5
#print axioms FRSB.Numbered.result_5_6
#print axioms FRSB.Numbered.result_6_1
#print axioms FRSB.Numbered.result_6_2
#print axioms FRSB.Numbered.result_6_3
#print axioms FRSB.Numbered.result_6_4
