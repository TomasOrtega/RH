import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SumDeg.exists_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsProductDegenerationDataSum.lean&line=541#L541)
-/
theorem _root_.GlobalTheory.T.exists_product_degenerationData_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I), ∃ (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ := by
  first | exact @GlobalTheory.SumDeg.exists_sum | exact GlobalTheory.SumDeg.exists_sum | (intros; apply GlobalTheory.SumDeg.exists_sum <;> assumption)
