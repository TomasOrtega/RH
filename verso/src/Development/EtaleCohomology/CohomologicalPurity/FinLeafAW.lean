import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutFin

namespace LateralTheory.Fin.LeafAW
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_purity_aw : LateralTheory.CohomologicalPurity.LeafAW := by
  apply LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafAW := etale_purity_aw
end LateralTheory.Fin.LeafAW
