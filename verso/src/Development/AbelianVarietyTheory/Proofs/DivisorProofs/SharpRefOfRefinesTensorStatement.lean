import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.PowData.sharpRef_of_tens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSharpRefOfRefinesTensor.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.sharpRef_of_refines_tensor : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_tens | exact GlobalTheory.Mum.PowData.sharpRef_of_tens | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_tens <;> assumption)
