import Development.EtaleCohomology.DivisorCycles.FinEmbedPf

namespace LateralTheory.Fin.FinEmbed
/- English proof (translation)
Apply `LateralTheory.DivDb.FinEmbedPf.FinEmbed_of` to reduce the goal to its premises.
-/
theorem etale_semisimple_finite_embedding_holds_assembled : LateralTheory.DivDb.FinEmbed := by
  apply LateralTheory.DivDb.FinEmbedPf.FinEmbed_of
/- English proof (translation)
The claim follows from `etale_semisimple_finite_embedding_holds_assembled`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinEmbed := etale_semisimple_finite_embedding_holds_assembled
end LateralTheory.Fin.FinEmbed
