import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToLocalRingOpenImmersion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLiftToLocalRingOpenImmersion.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.lift_to_local_ring_open_immersion : ∀ {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] {A : Type} [CommRing A] (ξ : Sp A ⟶ X)
    (𝔭 : PrimeSpectrum A), ξ 𝔭 ∈ Set.range j →
    ∃ y : Sp (Localization.AtPrime 𝔭.asIdeal) ⟶ U, y ≫ j = spMap (algebraMap A _) ≫ ξ := by
  first | exact @GlobalTheory.openImmersion_factor_localization_atPrime | exact GlobalTheory.openImmersion_factor_localization_atPrime | (intros; apply GlobalTheory.openImmersion_factor_localization_atPrime <;> assumption)
