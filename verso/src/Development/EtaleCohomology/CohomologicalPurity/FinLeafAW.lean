import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutFin

namespace LateralTheory.Fin.LeafAW
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of` to reduce the goal to its premises.
-/
theorem etale_purity_aw : LateralTheory.CohomologicalPurity.LeafAW := by
  apply LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of
/- English proof (translation)
The claim follows from `etale_purity_aw`.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafAW := etale_purity_aw
end LateralTheory.Fin.LeafAW
