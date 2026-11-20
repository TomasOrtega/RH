import Development.EtaleCohomology.CyclotomicDiscriminants.SFewOfCut

namespace LateralTheory.Fin.SFewOf
/- English proof (translation)
Apply `LateralTheory.Q.SFewOfCut.sFewOf` to reduce the goal to its premises.
-/
theorem few_of_statement_holds : UpperTheory.V.ZK.SFewOf := by
  apply LateralTheory.Q.SFewOfCut.sFewOf
/- English proof (translation)
The claim follows from `few_of_statement_holds`.
-/
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SFewOf := few_of_statement_holds
end LateralTheory.Fin.SFewOf
