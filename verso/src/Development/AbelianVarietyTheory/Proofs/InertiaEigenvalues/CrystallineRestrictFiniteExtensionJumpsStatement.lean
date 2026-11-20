import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Per.ResFinite.adm12_elementDenominator` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCrystallineRestrictFiniteExtensionJumps.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.crystalline_restrict_finite_extension_jumps : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  first | exact @GlobalTheory.Per.ResFinite.adm12_elementDenominator | exact GlobalTheory.Per.ResFinite.adm12_elementDenominator | (intros; apply GlobalTheory.Per.ResFinite.adm12_elementDenominator <;> assumption)
