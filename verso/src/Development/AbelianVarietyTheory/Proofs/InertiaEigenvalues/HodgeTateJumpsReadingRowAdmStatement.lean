import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdm
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHodgeTateJumpsReadingRowAdm.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.hodgeTateJumpsReading_rowAdm : ∀ D : D7, AdmissibleParameterJ.AdmRead D := by
  first | exact @GlobalTheory.AdmReadBridge.main | exact GlobalTheory.AdmReadBridge.main | (intros; apply GlobalTheory.AdmReadBridge.main <;> assumption)
