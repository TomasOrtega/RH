import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestAssumptionsOfThreeInterfaces
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestTCore
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColTop
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColumnPolynomialCovectorZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def GrowthBoundInterfaceConditions : Prop := RestCols ∧ RestPre ∧ RestTCore

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extendedClosedForm_of_interfaceConditions {D : Formalism.BasicNotions.D7} (h : admitted D → GrowthBoundInterfaceConditions) : ExtendedClosedForm D := stmtEExt_of_15c fun hA => rest_assumptions_of_three_interfaces hA (h hA).1 (h hA).2.1 (h hA).2.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parametersClosedForm_of_interfaceConditions {D : Formalism.BasicNotions.D7} (h : admitted D → GrowthBoundInterfaceConditions) : ClosedFormOfAdmitted D := stmtE_of_15c fun hA => rest_assumptions_of_three_interfaces hA (h hA).1 (h hA).2.1 (h hA).2.2

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem growthBoundInterfaceConditions : GrowthBoundInterfaceConditions := ⟨restCols, restPre, restTCore⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem asmRTCondition_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : RestAsmRT := rest_assumptions_of_three_interfaces hA restCols restPre restTCore

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extendedClosedForm (D : Formalism.BasicNotions.D7) : ExtendedClosedForm D := extendedClosedForm_of_interfaceConditions fun _ => growthBoundInterfaceConditions

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stmtE_proved (D : Formalism.BasicNotions.D7) : ClosedFormOfAdmitted D := parametersClosedForm_of_interfaceConditions fun _ => growthBoundInterfaceConditions

end Formalism.MainNotions.ColumnSystems.Pf
