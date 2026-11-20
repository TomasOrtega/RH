import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CFxi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointCompStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

/- English proof (translation)
Introduce `R _ _ I D D' F`. Use `haveI := F.inc_hom`. Use `haveI := F.o.onB.hom F.f`. Establish `hm : IsMonHom (F.inc ≫ F.o.onB.act F.f)` using `inferInstance`. Establish `H` using `GlobalTheory.T.of_twisted_adjoint_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e)) (F.inc ≫ F.o.onB.act F.f) F.xp (DistribMulAction.toAddMonoidHom D'.toPre.X F.e) (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e)) ((DistribMulAction.toAddMono …`.

Establish `e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f)`. Rewrite using `[F.o.onB.map_mul, Category.assoc]`. Establish `e2 : (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp ((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) = (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi`. Use extensionality with `y`. Simplify using `[mul_smul]`.

Conclude with `e1 ▸ e2 ▸ H`.
-/
theorem factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  intro R _ _ I D D' F
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  have hm : IsMonHom (F.inc ≫ F.o.onB.act F.f) := inferInstance
  have H := GlobalTheory.T.of_twisted_adjoint_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e))
    (F.inc ≫ F.o.onB.act F.f) F.xp
    (DistribMulAction.toAddMonoidHom D'.toPre.X F.e) (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e))
    ((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) F.pr_hom hm
    (fun y => c_xp F y) (fun z => c_fxi F z) (GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair R I D' F.O F.o F.e) (GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback R I D D' F)
  have e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f) := by
    rw [F.o.onB.map_mul, Category.assoc]
  have e2 : (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp
      ((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) =
      (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi := by
    ext y
    simp [mul_smul]
  exact e1 ▸ e2 ▸ H

end GlobalTheory.MumFam.FactorAdj
