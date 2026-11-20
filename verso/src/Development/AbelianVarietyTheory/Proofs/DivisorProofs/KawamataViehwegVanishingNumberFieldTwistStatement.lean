import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKawamataViehwegVanishingNumberFieldTwist.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  first | exact @GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | exact GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | (intros; apply GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj <;> assumption)
