import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExtCrysCrit.blochKato_ext_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBlochKatoCrystallineExtensionCriterion.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.blochKato_crystalline_extension_criterion : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  first | exact @GlobalTheory.ExtCrysCrit.blochKato_ext_all | exact GlobalTheory.ExtCrysCrit.blochKato_ext_all | (intros; apply GlobalTheory.ExtCrysCrit.blochKato_ext_all <;> assumption)
