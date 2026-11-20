import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEq
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGrpPullbackDivisionPointsPushEq.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.grpPullback_divisionPoints_push_eq : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  first | exact @GlobalTheory.DivPush.push_div_pts | exact GlobalTheory.DivPush.push_div_pts | (intros; apply GlobalTheory.DivPush.push_div_pts <;> assumption)
