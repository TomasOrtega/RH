import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FThetaLiftHasPointAtLocalisationSamePlace.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.theta_lift_has_point_at_localisation_same_place : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i), thetaOf D.nd D.naut i σ P → ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ (P' : D.naut.AV i') (x' : D.nd.X i'), thetaOf D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  first | exact @GlobalTheory.LiftPoint.main | exact GlobalTheory.LiftPoint.main | (intros; apply GlobalTheory.LiftPoint.main <;> assumption)
