import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LemmaA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SBasis
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ClosureBasicModules
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement

namespace Formalism.InvariantFactorPaths.ColumnFamilies.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaA : LemmaA := claimA_straightening
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sBasis : SBasis := standard_basis_theorem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem closure_first_part : ClosureBasicModules := closure_first_part_of claimA_straightening standard_basis_theorem

end Formalism.InvariantFactorPaths.ColumnFamilies.Top
