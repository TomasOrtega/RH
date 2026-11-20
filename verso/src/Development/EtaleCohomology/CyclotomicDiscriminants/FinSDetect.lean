import Development.EtaleCohomology.CyclotomicDiscriminants.SDetectCut

namespace LateralTheory.Fin.SDetect
/- English proof (translation)
Apply `LateralTheory.Q.SDetectCut.goal` to reduce the goal to its premises.
-/
theorem detection_statement_holds : UpperTheory.V.ZK.SDetect := by
  apply LateralTheory.Q.SDetectCut.goal
/- English proof (translation)
The claim follows from `detection_statement_holds`.
-/
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SDetect := detection_statement_holds
end LateralTheory.Fin.SDetect
