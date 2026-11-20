import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodReductionStableValuationRingExtension
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
Apply `GlobalTheory.GoodBaseChange.good_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FGoodReductionStableValuationRingExtension.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.goodReduction_stable_valuationRing_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  first | exact @GlobalTheory.GoodBaseChange.good_baseChange | exact GlobalTheory.GoodBaseChange.good_baseChange | (intros; apply GlobalTheory.GoodBaseChange.good_baseChange <;> assumption)
