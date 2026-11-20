import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SymGrpPull.symm_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSymmetricLineBundlePullbackGrpPullback.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  first | exact @GlobalTheory.SymGrpPull.symm_pull | exact GlobalTheory.SymGrpPull.symm_pull | (intros; apply GlobalTheory.SymGrpPull.symm_pull <;> assumption)
