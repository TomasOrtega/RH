import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackThetaFamilyGaloisTwistBijective.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (famTw D N σ) := by
  first | exact @GlobalTheory.Mum.Conj.FamBij.famTw_bijective | exact GlobalTheory.Mum.Conj.FamBij.famTw_bijective | (intros; apply GlobalTheory.Mum.Conj.FamBij.famTw_bijective <;> assumption)
