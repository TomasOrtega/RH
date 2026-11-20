import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelGenericSpecialDvr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalModelGenericSpecialDvr.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.normal_model_generic_special_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ η : B.X, IsGenSpecial B η → IsDiscreteValuationRing (B.X.presheaf.stalk η) := by
  first | exact @GlobalTheory.GenSpecialDvr.isDiscreteValuationRing_stalk | exact GlobalTheory.GenSpecialDvr.isDiscreteValuationRing_stalk | (intros; apply GlobalTheory.GenSpecialDvr.isDiscreteValuationRing_stalk <;> assumption)
