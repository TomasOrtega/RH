import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeatMod.TorField.exists_torTan_of_q` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTorusTangentOfRaynaudTangentOverUnit.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  first | exact @GlobalTheory.HeatMod.TorField.exists_torTan_of_q | exact GlobalTheory.HeatMod.TorField.exists_torTan_of_q | (intros; apply GlobalTheory.HeatMod.TorField.exists_torTan_of_q <;> assumption)
