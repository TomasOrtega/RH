import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackThetaFamilyGaloisTwistSemilinearSmul.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N), Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  first | exact @GlobalTheory.Mum.Conj.famTw_isSmul | exact GlobalTheory.Mum.Conj.famTw_isSmul | (intros; apply GlobalTheory.Mum.Conj.famTw_isSmul <;> assumption)
