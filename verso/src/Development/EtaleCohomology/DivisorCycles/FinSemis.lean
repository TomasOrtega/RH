import Development.EtaleCohomology.DivisorCycles.SemisPf

namespace LateralTheory.Fin.Semis
/- English proof (translation)
Apply `LateralTheory.DivDb.SemisPf.Semis_of` to reduce the goal to its premises.
-/
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
/- English proof (translation)
The claim follows from `etale_semisimplicity_instance`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Semis := etale_semisimplicity_instance
end LateralTheory.Fin.Semis
