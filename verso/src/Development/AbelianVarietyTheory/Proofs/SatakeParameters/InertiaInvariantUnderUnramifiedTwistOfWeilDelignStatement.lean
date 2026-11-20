import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FInertiaInvariantUnderUnramifiedTwistOfWeilDelign.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := by
  first | exact @GlobalTheory.IneUnrTwist.main | exact GlobalTheory.IneUnrTwist.main | (intros; apply GlobalTheory.IneUnrTwist.main <;> assumption)
