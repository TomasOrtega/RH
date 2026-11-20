import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSphericalHeckeScalarOnTypeSpacesAllPlaces.lean&line=332#L332)
-/
theorem _root_.GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ i : D.nd.Loc, HeckeScalar M i := by
  first | exact @GlobalTheory.HeckeScalarAll.heckeScalar_all | exact GlobalTheory.HeckeScalarAll.heckeScalar_all | (intros; apply GlobalTheory.HeckeScalarAll.heckeScalar_all <;> assumption)
