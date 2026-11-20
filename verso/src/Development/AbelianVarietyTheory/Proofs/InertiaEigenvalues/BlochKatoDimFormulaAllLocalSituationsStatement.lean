import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimFormulaAllLocalSituations
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBlochKatoDimFormulaAllLocalSituations.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.blochKato_dimFormula_all_localSituations : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  first | exact @GlobalTheory.blochKatoDim_at_every_local_situation | exact GlobalTheory.blochKatoDim_at_every_local_situation | (intros; apply GlobalTheory.blochKatoDim_at_every_local_situation <;> assumption)
