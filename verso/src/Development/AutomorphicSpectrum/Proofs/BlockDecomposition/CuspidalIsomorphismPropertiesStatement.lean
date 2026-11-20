import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismProperties
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalIsomorphismProperties.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.cuspidal_isomorphism_properties : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | exact GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts <;> assumption)
