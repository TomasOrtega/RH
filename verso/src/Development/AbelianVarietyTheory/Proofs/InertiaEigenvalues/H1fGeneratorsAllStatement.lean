import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAll
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FH1fGeneratorsAll.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm13 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  first | exact @GlobalTheory.h1f_generators_of_record | exact GlobalTheory.h1f_generators_of_record | (intros; apply GlobalTheory.h1f_generators_of_record <;> assumption)
