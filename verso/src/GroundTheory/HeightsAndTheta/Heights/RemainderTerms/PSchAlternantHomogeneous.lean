import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

/- English proof (translation)
Introduce `ι _ _ e`. Unfold `alternant`. Rewrite using `[Matrix.det_apply]`. Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `σ _`.

Establish `h : IsHomogeneous (∏ i, (X (σ i) : MvPolynomial ι ℚ) ^ e i) (∑ i, e i)` using `IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X_pow _ _)`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>`. Simplify using `only [hs, Matrix.of_apply, one_smul, Units.neg_smul]`. Conclude with `h`. Conclude with `h.neg`.
-/
theorem SchAlternantHomogeneous.proof : SchAlternantHomogeneous.Statement := by
  intro ι _ _ e
  unfold alternant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have h : IsHomogeneous (∏ i, (X (σ i) : MvPolynomial ι ℚ) ^ e i) (∑ i, e i) :=
    IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X_pow _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, Matrix.of_apply, one_smul, Units.neg_smul]
  · exact h
  · exact h.neg

end GroundTheory.Heights₂.Heights.RestTerms
