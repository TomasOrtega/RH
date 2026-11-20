import Development.EtaleCohomology.CyclotomicDiscriminants.SLayerCut

namespace LateralTheory.Fin.SLayer
/- English proof (translation)
Apply `LateralTheory.Q.SLayerCut.goal_of` to reduce the goal to its premises.
-/
theorem layer_statement_holds : UpperTheory.V.ZK.SLayer := by
  apply LateralTheory.Q.SLayerCut.goal_of
/- English proof (translation)
The claim follows from `layer_statement_holds`.
-/
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SLayer := layer_statement_holds
end LateralTheory.Fin.SLayer
