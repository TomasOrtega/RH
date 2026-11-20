import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryIrreducibleIsAdmissible.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.unitary_irreducible_is_admissible : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  first | exact @GlobalTheory.IrrAdm.isIrrAdm_of_irred | exact GlobalTheory.IrrAdm.isIrrAdm_of_irred | (intros; apply GlobalTheory.IrrAdm.isIrrAdm_of_irred <;> assumption)
