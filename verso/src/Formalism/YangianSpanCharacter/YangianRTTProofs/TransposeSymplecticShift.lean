import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.P

open Matrix

/- English proof (translation)
Introduce `R A _ _ _ p c ci Y h`. Take `⟨h1, h2, h3⟩` from `h`. Establish `hpci : p * ci = ci * p - ci`. Establish `: ci * (p * c) * ci = ci * (c * p + c) * ci` using `by rw [h3]`. Establish `e1 : ci * (p * c) * ci = ci * p`.

Rewrite using `[mul_assoc, mul_assoc, h1, mul_one]`. Establish `e2 : ci * (c * p + c) * ci = p * ci + ci`. Rewrite using `[mul_add, add_mul, ← mul_assoc ci c p, h2, one_mul, one_mul]`. Rewrite `this` using `[e1, e2]`. Rewrite using `[this]`.

Normalize the expressions using the abelian group laws. Establish `hc : ∀ x : A, algebraMap R A Y * x = x * algebraMap R A Y` using `fun x => Algebra.commutes Y x`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]`.

Apply the tactic sequence `all_goals first`. Consider the case `exact h1`. Consider the case `exact h2`. Consider the case `(rw [hpci, hc ci]; abel)`.
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
Introduce `R A _ _ _ p c ci f s Y hfc hfci hpf`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`. Simplify using `[Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`.

Simplify using `[Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `key : c * f * algebraMap R A s = algebraMap R A s * f * c`. Rewrite using `[← hfc, mul_assoc, ← Algebra.commutes, ← mul_assoc]`. Conclude with `congrArg (· * c) (Algebra.commutes s f).symm`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two, hfc, hfci] <;>`. Apply the tactic sequence `simp only [mul_add, add_mul, mul_neg, neg_mul, hpf, key, Algebra.commutes] <;>`. Apply the tactic sequence `first | noncomm_ring | abel`.
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
Introduce `R A _ _ _ s`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem unipotentSymplectic : Formalism.YangianSpanCharacter.T.UJU := by
  intro R A _ _ _ s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun f => funext fun n => ?_` and prove the remaining obligations. Simplify using `[Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]`. Use `LinearMap.ext fun f => funext fun n => ?_` and prove the remaining obligations. Simplify using `[Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]`.

Use `LinearMap.ext fun f => funext fun n => ?_` and prove the remaining obligations. Simplify using `[Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.pM, LinearMap.funLeft_apply]`. Expand and normalize the polynomial expressions, which then agree.
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
