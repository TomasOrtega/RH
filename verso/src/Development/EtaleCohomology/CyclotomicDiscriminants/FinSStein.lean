import Development.EtaleCohomology.CyclotomicDiscriminants.SSteinTPf

namespace LateralTheory.Fin.SStein
/- English proof (translation)
Apply `LateralTheory.Q.SSteinT.SStein_of` to reduce the goal to its premises.
-/
theorem stein_statement_holds : UpperTheory.V.ZK.SStein := by
  apply LateralTheory.Q.SSteinT.SStein_of
/- English proof (translation)
The claim follows from `stein_statement_holds`.
-/
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SStein := stein_statement_holds
end LateralTheory.Fin.SStein
