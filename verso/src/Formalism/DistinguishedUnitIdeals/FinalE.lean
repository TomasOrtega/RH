import Mathlib
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.RhoMapFunctorial
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.SplittingOfPositiveLevel
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.BaseGamC

namespace Formalism.ExponentWindows.E

/- English proof (translation)
The claim follows from `thmE_of rho_map_exists rho_map_linear rho_map_functorial splitting_of_extension`.
-/
theorem theorem_E_assembled : ThmEAssembly :=
  thmE_of rho_map_exists rho_map_linear rho_map_functorial splitting_of_extension

/- English proof (translation)
Assemble the required witnesses or components as `⟨rho_map_exists, rho_map_linear, rho_map_functorial, splitting_of_extension, theorem_E_assembled⟩`.
-/
theorem theorem_E_all_parts : RhoExists ∧ RhoLin ∧ RhoFun ∧ Step1 ∧ ThmEAssembly :=
  ⟨rho_map_exists, rho_map_linear, rho_map_functorial, splitting_of_extension, theorem_E_assembled⟩

end Formalism.ExponentWindows.E
