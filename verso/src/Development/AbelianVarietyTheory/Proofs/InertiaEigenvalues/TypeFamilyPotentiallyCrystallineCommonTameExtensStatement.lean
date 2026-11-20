import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtens
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PotDirect.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTypeFamilyPotentiallyCrystallineCommonTameExtens.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension : StepPotDirect := by
  first | exact @GlobalTheory.PotDirect.main | exact GlobalTheory.PotDirect.main | (intros; apply GlobalTheory.PotDirect.main <;> assumption)
