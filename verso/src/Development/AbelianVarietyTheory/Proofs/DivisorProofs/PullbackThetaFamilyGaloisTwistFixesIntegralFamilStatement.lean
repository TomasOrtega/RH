import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackThetaFamilyGaloisTwistFixesIntegralFamil.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  first | exact @GlobalTheory.Mum.Conj.famTw_eq_of_over | exact GlobalTheory.Mum.Conj.famTw_eq_of_over | (intros; apply GlobalTheory.Mum.Conj.famTw_eq_of_over <;> assumption)
