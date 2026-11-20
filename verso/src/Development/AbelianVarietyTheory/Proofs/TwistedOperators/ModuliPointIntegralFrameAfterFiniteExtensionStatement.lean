import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
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
Apply `GlobalTheory.AnyLevelFrame.intFrExt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FModuliPointIntegralFrameAfterFiniteExtension.lean&line=300#L300)
-/
theorem _root_.GlobalTheory.T.moduliPoint_integralFrame_after_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → IntFrExt Xo c := by
  first | exact @GlobalTheory.AnyLevelFrame.intFrExt | exact GlobalTheory.AnyLevelFrame.intFrExt | (intros; apply GlobalTheory.AnyLevelFrame.intFrExt <;> assumption)
