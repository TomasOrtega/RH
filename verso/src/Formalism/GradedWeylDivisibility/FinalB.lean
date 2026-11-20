import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLine
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLineTall
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQPos
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQBilin
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivClosedGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWInClosed
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaTallZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylEqNablaQ
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRationalOf

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwLine : HWLine := highest_weight_line
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwLineTall : HWLineTall := highest_weight_line_tall
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockQPos : FockQPos := fischerInnerRatPos
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockQBilin : FockQBilin := fischerInnerRatBilinear
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockQRowDivAdj : FockQRowDivAdj := fock_space_row_divided_adjoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rowDivClosedGraded : RowDivClosedGraded := row_divided_closed_graded
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwInClosed : HWInClosed := hwInClosed_of hwLine rowDivClosedGraded
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem closedEqNabla : ClosedEqNabla := closedEqNabla_of hwInClosed fockQPos fockQBilin fockQRowDivAdj
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylEqNablaQ : WeylEqNablaQ := weylEqNablaQ_of closedEqNabla

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylRational : WeylRational := weyl_module_rational weylEqNablaQ

end Formalism.GradedWeylDivisibility
