import Development.EtaleCohomology.DivisorCycles.MinCongr

namespace LateralTheory.Fin.Rep
/- English proof (translation)
Apply `LateralTheory.DivDb.RepPf.Rep_of` to reduce the goal to its premises.
-/
theorem etale_representation_realization_instance : LateralTheory.DivDb.Rep := by
  apply LateralTheory.DivDb.RepPf.Rep_of
/- English proof (translation)
The claim follows from `etale_representation_realization_instance`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Rep := etale_representation_realization_instance
end LateralTheory.Fin.Rep
