import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextension
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
Apply `GlobalTheory.HkIntegral.frPt_descends_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFramedPointDescendsFiniteSubextension.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.framedPoint_descends_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  first | exact @GlobalTheory.HkIntegral.frPt_descends_finite | exact GlobalTheory.HkIntegral.frPt_descends_finite | (intros; apply GlobalTheory.HkIntegral.frPt_descends_finite <;> assumption)
