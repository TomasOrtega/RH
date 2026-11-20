import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobInt.frobenius_integrality` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusIntegralityWittTiltAinf.lean&line=273#L273)
-/
theorem _root_.GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf : ∀ (l : ℕ) [Fact l.Prime] (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (WCb l)) (S : Matrix p p (Ainf l)) (S' : Matrix q q (Ainf l)) (Y : Matrix p q (Ainf l)), Z.map (frobW l) = S.map (inclW l) * Z * S'.map (inclW l) + Y.map (inclW l) → ∀ a b, Z a b ∈ Set.range (inclW l) := by
  first | exact @GlobalTheory.FrobInt.frobenius_integrality | exact GlobalTheory.FrobInt.frobenius_integrality | (intros; apply GlobalTheory.FrobInt.frobenius_integrality <;> assumption)
