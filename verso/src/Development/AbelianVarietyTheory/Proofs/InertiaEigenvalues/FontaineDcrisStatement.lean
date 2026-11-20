import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFontaineDcris.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm11 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  first | exact @GlobalTheory.Per.DcrisExact.fontaine_dcris | exact GlobalTheory.Per.DcrisExact.fontaine_dcris | (intros; apply GlobalTheory.Per.DcrisExact.fontaine_dcris <;> assumption)
