import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtens
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.PotDirect.main | exact GlobalTheory.PotDirect.main | (intros; apply GlobalTheory.PotDirect.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension : StepPotDirect := by
  first | exact @GlobalTheory.PotDirect.main | exact GlobalTheory.PotDirect.main | (intros; apply GlobalTheory.PotDirect.main <;> assumption)
