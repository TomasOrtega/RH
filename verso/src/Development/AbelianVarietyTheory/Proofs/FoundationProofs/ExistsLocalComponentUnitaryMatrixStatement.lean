import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLocalComponentUnitaryMatrix.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.exists_local_component_unitary_matrix : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  first | exact @GlobalTheory.LocalComponent.exists_local_component | exact GlobalTheory.LocalComponent.exists_local_component | (intros; apply GlobalTheory.LocalComponent.exists_local_component <;> assumption)
