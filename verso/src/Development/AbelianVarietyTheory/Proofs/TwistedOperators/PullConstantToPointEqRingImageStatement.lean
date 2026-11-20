import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PullConstantToPointEqRingImage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPullConstantToPointEqRingImage.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.pull_constant_to_point_eq_ring_image : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  first | exact @GlobalTheory.PullConst.pull_const_apply | exact GlobalTheory.PullConst.pull_const_apply | (intros; apply GlobalTheory.PullConst.pull_const_apply <;> assumption)
