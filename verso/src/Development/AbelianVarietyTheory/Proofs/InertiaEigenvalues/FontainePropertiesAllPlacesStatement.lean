import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFontainePropertiesAllPlacesAlt.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.fontaineAtPlacesOverL : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := by
  first | exact @GlobalTheory.FontaineAdm.fontaineProperties_all_places | exact GlobalTheory.FontaineAdm.fontaineProperties_all_places | (intros; apply GlobalTheory.FontaineAdm.fontaineProperties_all_places <;> assumption)
