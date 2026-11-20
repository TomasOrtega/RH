import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LemmaA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SBasis
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ClosureBasicModules
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement

namespace Formalism.InvariantFactorPaths.ColumnFamilies.Top

/- English proof (translation)
The claim follows from `claimA_straightening`.
-/
theorem lemmaA : LemmaA := claimA_straightening
/- English proof (translation)
The claim follows from `standard_basis_theorem`.
-/
theorem sBasis : SBasis := standard_basis_theorem
/- English proof (translation)
The claim follows from `closure_first_part_of claimA_straightening standard_basis_theorem`.
-/
theorem closure_first_part : ClosureBasicModules := closure_first_part_of claimA_straightening standard_basis_theorem

end Formalism.InvariantFactorPaths.ColumnFamilies.Top
