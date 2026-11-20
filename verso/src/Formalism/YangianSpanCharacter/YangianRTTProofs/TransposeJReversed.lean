import Formalism.YangianSpanCharacter.TJTrev

namespace Formalism.YangianSpanCharacter.P

open Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem transpose_j_reversed : Formalism.YangianSpanCharacter.T.TJTrev := by
  intro R A _ _ _ q d di Y h1 h2 h3
  have hc : algebraMap R A Y * d = d * algebraMap R A Y := Algebra.commutes Y d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [h3, hc]; abel)

end Formalism.YangianSpanCharacter.P
