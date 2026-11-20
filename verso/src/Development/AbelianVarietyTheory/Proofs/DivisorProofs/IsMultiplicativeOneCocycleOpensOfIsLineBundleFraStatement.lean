import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiplicativeOneCocycleOpensOfIsLineBundleFra
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsMultiplicativeOneCocycleOpensOfIsLineBundleFra.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  first | exact @GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame | exact GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame | (intros; apply GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame <;> assumption)
