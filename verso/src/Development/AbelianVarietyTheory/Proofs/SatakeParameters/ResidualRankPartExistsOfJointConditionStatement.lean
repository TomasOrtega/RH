import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FResidualRankPartExistsOfJointCondition.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)
