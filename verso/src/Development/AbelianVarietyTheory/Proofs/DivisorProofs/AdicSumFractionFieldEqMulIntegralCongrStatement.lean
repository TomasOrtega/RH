import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.AdicTerm.sumF_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdicSumFractionFieldEqMulIntegralCongr.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  first | exact @GlobalTheory.Poinc.AdicTerm.sumF_mul | exact GlobalTheory.Poinc.AdicTerm.sumF_mul | (intros; apply GlobalTheory.Poinc.AdicTerm.sumF_mul <;> assumption)
