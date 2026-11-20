import Mathlib
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.RhoMapFunctorial
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.SplittingOfPositiveLevel
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.BaseGamC

namespace Formalism.ExponentWindows.E

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theorem_E_assembled : ThmEAssembly :=
  thmE_of rho_map_exists rho_map_linear rho_map_functorial splitting_of_extension

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem theorem_E_all_parts : RhoExists ∧ RhoLin ∧ RhoFun ∧ Step1 ∧ ThmEAssembly :=
  ⟨rho_map_exists, rho_map_linear, rho_map_functorial, splitting_of_extension, theorem_E_assembled⟩

end Formalism.ExponentWindows.E
