import Development.EtaleCohomology.DivisorCycles.FinEmbedPf

namespace LateralTheory.Fin.FinEmbed
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_semisimple_finite_embedding_holds_assembled : LateralTheory.DivDb.FinEmbed := by
  apply LateralTheory.DivDb.FinEmbedPf.FinEmbed_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinEmbed := etale_semisimple_finite_embedding_holds_assembled
end LateralTheory.Fin.FinEmbed
