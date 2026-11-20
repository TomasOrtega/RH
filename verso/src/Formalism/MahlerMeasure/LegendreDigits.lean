import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm
import Formalism.MahlerMeasure.MahlerMeasureProofs.TrueRing
import Formalism.MahlerMeasure.MahlerMeasureProofs.Mahler
import Mathlib

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
The claim follows from `determinant_block_leading_term`.
-/
theorem detBlockLead : DetBlockLead := determinant_block_leading_term
end Formalism.GM.Top
