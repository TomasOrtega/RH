import Development.EtaleCohomology.EtaleSheaves.ValSuccAbove

namespace LateralTheory.Fin.EtaleChapterDThree
/- English proof (translation)
Apply `LateralTheory.E.t_D3Cut.goal` to reduce the goal to its premises.
-/
theorem etale_cohomology_third_statement_holds_alt : LateralTheory.E.EtaleChapterDThree := by
  apply LateralTheory.E.t_D3Cut.goal
/- English proof (translation)
The claim follows from `etale_cohomology_third_statement_holds_alt`.
-/
theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDThree := etale_cohomology_third_statement_holds_alt
end LateralTheory.Fin.EtaleChapterDThree
