import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply `GlobalTheory.kTriv_boxLB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FKTrivExternalTensorPowerLineBundle.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.kTriv_external_tensor_power_lineBundle : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  first | exact @GlobalTheory.kTriv_boxLB | exact GlobalTheory.kTriv_boxLB | (intros; apply GlobalTheory.kTriv_boxLB <;> assumption)
