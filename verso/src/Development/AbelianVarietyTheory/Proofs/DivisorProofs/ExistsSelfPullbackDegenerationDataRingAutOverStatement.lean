import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfPullbackDegenerationDataRingAutOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSelfPullbackDegenerationDataRingAutOver.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  first | exact @GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | exact GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | (intros; apply GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver <;> assumption)
