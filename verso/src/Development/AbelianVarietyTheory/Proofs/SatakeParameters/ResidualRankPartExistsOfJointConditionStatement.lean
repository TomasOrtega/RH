import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)
