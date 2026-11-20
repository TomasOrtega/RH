import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PresCharts.exists_charts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsChartsSquareZeroPresentedScheme.lean&line=159#L159)
-/
theorem _root_.GlobalTheory.T.exists_charts_squareZero_presented_scheme : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i), IsPullback i s₀ s (spMap π) → ∃ (V : AffOp X₀ → X.Opens) (hV : ∀ ⦃T T' : AffOp X₀⦄, (T ⟶ T') → V T' ≤ V T) (hi : ∀ T, T.unop.1 ≤ i ⁻¹ᵁ V T) (e : ∀ T, S.F.obj T →+* Γ(X, V T)), (∀ T, i ⁻¹ᵁ V T = T.unop.1) ∧ (∀ (T T' : AffOp X₀) (a : T ⟶ T') (b : S.F.obj T), e T' (mp S.F a b) = resG X (hV a) (e T b)) ∧ ∀ T b, (i.appLE (V T) T.unop.1 (hi T)).hom (e T b) = S.p T b := by
  first | exact @GlobalTheory.PresCharts.exists_charts | exact GlobalTheory.PresCharts.exists_charts | (intros; apply GlobalTheory.PresCharts.exists_charts <;> assumption)
