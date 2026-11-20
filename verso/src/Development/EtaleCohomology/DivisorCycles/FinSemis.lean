import Development.EtaleCohomology.DivisorCycles.SemisPf

namespace LateralTheory.Fin.Semis
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Semis := etale_semisimplicity_instance
end LateralTheory.Fin.Semis
