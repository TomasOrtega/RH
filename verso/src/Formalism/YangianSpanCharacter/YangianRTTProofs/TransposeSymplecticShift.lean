import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.P

open Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Establish an intermediate fact. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem transposeSymplecticShift : Formalism.YangianSpanCharacter.T.TJT := by
  intro R A _ _ _ p c ci Y h
  obtain ⟨h1, h2, h3⟩ := h
  have hpci : p * ci = ci * p - ci := by
    have : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
    have e1 : ci * (p * c) * ci = ci * p := by
      rw [mul_assoc, mul_assoc, h1, mul_one]
    have e2 : ci * (c * p + c) * ci = p * ci + ci := by
      rw [mul_add, add_mul, ← mul_assoc ci c p, h2, one_mul, one_mul]
    rw [e1, e2] at this
    rw [this]; abel
  have hc : ∀ x : A, algebraMap R A Y * x = x * algebraMap R A Y := fun x => Algebra.commutes Y x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [hpci, hc ci]; abel)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.

Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem planeWaveIntertwining : Formalism.YangianSpanCharacter.T.PlaneWave := by
  intro R A _ _ _ p c ci f s Y hfc hfci hpf
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · have key : c * f * algebraMap R A s = algebraMap R A s * f * c := by
      rw [← hfc, mul_assoc, ← Algebra.commutes, ← mul_assoc]
      exact congrArg (· * c) (Algebra.commutes s f).symm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two, hfc, hfci] <;>
      simp only [mul_add, add_mul, mul_neg, neg_mul, hpf, key, Algebra.commutes] <;>
      first | noncomm_ring | abel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem unipotentSymplectic : Formalism.YangianSpanCharacter.T.UJU := by
  intro R A _ _ _ s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isWeylTripleShiftModel : Formalism.YangianSpanCharacter.T.WeylModel := by
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.pM, LinearMap.funLeft_apply]
    ring

end Formalism.YangianSpanCharacter.P
