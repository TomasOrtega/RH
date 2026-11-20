import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelRankDegreeShareLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithHilbertSamuelRankDegreeShareLe.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F), IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d := by
  first | exact @GlobalTheory.HSCore.share_le | exact GlobalTheory.HSCore.share_le | (intros; apply GlobalTheory.HSCore.share_le <;> assumption)
