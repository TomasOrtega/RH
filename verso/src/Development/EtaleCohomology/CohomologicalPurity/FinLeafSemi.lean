import Development.EtaleCohomology.CohomologicalPurity.LeafSemiPf

namespace LateralTheory.Fin.LeafSemi
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafSemi_of` to reduce the goal to its premises.
-/
theorem etale_purity_semilocal_of_reduction : LateralTheory.CohomologicalPurity.LeafSemi := by
  apply LateralTheory.CohomologicalPurity.LeafSemi_of
/- English proof (translation)
The claim follows from `etale_purity_semilocal_of_reduction`.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafSemi := etale_purity_semilocal_of_reduction
end LateralTheory.Fin.LeafSemi
