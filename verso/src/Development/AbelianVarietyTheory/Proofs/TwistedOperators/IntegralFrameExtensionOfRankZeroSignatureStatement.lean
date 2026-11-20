import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralFrameExtensionOfRankZeroSignature.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.integralFrameExtension_of_rank_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  first | exact @GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | exact GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | (intros; apply GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero <;> assumption)
