import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarev
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FThetaLocusDecomposesOverCoefRingOfChebotarev.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D → ∀ i : D.nd.Loc, ZDecomp D.nd i := by
  first | exact @GlobalTheory.ZDecompAt.zDecomp_of_cheb | exact GlobalTheory.ZDecompAt.zDecomp_of_cheb | (intros; apply GlobalTheory.ZDecompAt.zDecomp_of_cheb <;> assumption)
