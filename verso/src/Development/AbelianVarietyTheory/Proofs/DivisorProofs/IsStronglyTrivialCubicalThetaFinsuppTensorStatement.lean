import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsStronglyTrivialCubicalThetaFinsuppTensor.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  first | exact @GlobalTheory.TensBal.triv_theta | exact GlobalTheory.TensBal.triv_theta | (intros; apply GlobalTheory.TensBal.triv_theta <;> assumption)
