import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFunctionFieldMapDoubleSpaceGenericPoint.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt → ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  first | exact @GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint | exact GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint | (intros; apply GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint <;> assumption)
