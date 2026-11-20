import Development.EtaleCohomology.CyclotomicDiscriminants.SRelTPf

namespace LateralTheory.Fin.SRel
/- English proof (translation)
Apply `LateralTheory.Q.SRelT.SRel_of` to reduce the goal to its premises.
-/
theorem relation_statement_holds : UpperTheory.V.ZK.SRel := by
  apply LateralTheory.Q.SRelT.SRel_of
/- English proof (translation)
The claim follows from `relation_statement_holds`.
-/
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SRel := relation_statement_holds
end LateralTheory.Fin.SRel
