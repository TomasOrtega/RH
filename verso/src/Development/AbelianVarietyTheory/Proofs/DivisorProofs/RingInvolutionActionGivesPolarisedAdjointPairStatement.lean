import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MumFam.adj_act` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingInvolutionActionGivesPolarisedAdjointPair.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribMulAction.toAddMonoidHom D.toPre.X a) (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) := by
  first | exact @GlobalTheory.MumFam.adj_act | exact GlobalTheory.MumFam.adj_act | (intros; apply GlobalTheory.MumFam.adj_act <;> assumption)
