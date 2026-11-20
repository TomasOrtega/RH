import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGenerator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharKer.triv_of_isPullGen_of_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleTrivialOfInvariantPullbackGenerator.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  first | exact @GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | exact GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | (intros; apply GlobalTheory.CharKer.triv_of_isPullGen_of_invariant <;> assumption)
