import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.HomExtendsOverDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.HomExtExamples

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem homExtendsOverDVR_holds : GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR.HomExtendsOverDVR :=
  fun T _ _ _ K _ _ _ G G' _ _ => GlobalTheory.semiAbelian_hom_extends_uniquely_dvr T K G G'

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem homExtendsOverDVR_iff : GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR.HomExtendsOverDVR ↔ GlobalTheory.LN.HomExtSt :=
  ⟨fun h T K _ _ _ _ _ _ => h T K, fun h T _ _ _ K => h T K⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homExtSt_holds : GlobalTheory.LN.HomExtSt := homExtendsOverDVR_iff.1 homExtendsOverDVR_holds

end GlobalTheory.HomExtExamples
