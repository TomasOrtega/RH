import Development.EtaleCohomology.CohomologicalPurity.LeafAWCut
import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw

/- English proof (translation)
The claim follows from `LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec`.
-/
theorem LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of : LateralTheory.CohomologicalPurity.LeafAW :=
  LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec
