import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.PieriColumnMinors.PathEqOfContentSequence
import Formalism.PieriBlockIdeals.PieriColumnMinors.AntitoneShapes
import Formalism.PieriBlockIdeals.PieriColumnMinors.PermutationWeightInvariant
import Formalism.PieriBlockIdeals.PieriColumnMinors.MeasureSwapInvariant

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
The claim follows from `AntiStep_of no_bad_tuple`.
-/
theorem antitone_increment : AntiStep := AntiStep_of no_bad_tuple

/- English proof (translation)
The claim follows from `ColumnsFromPieri_of swap_path_exists same_column measure_swap_invariant monotone_run weight_iff_condition good_swap_exists antitone_increment antitone_shapes`.
-/
theorem columns_from_pieri : ColumnsFromPieri :=
  ColumnsFromPieri_of swap_path_exists same_column measure_swap_invariant monotone_run weight_iff_condition good_swap_exists
    antitone_increment antitone_shapes

/- English proof (translation)
The claim follows from `LemmaDSkeleton4_of columns_from_pieri`.
-/
theorem lemma_d_skeleton_four : LemmaDSkeleton4 := LemmaDSkeleton4_of columns_from_pieri

end Formalism.CohomologicalDescent.LC
