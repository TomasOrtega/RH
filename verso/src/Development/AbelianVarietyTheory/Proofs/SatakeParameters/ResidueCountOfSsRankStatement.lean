import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResidualRankCount.residual_count` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FResidueCountOfSsRank.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.residue_count_of_ss_rank : ValRingModel → SSList → SSRankUnique → ResCount := by
  first | exact @GlobalTheory.ResidualRankCount.residual_count | exact GlobalTheory.ResidualRankCount.residual_count | (intros; apply GlobalTheory.ResidualRankCount.residual_count <;> assumption)
