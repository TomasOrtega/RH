import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpEighthPowerRelativeDimensionEqEightMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.Sep.sharpRef_relDim` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSharpEighthPowerRelativeDimensionEqEightMul.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  first | exact @GlobalTheory.Poinc.Sep.sharpRef_relDim | exact GlobalTheory.Poinc.Sep.sharpRef_relDim | (intros; apply GlobalTheory.Poinc.Sep.sharpRef_relDim <;> assumption)
