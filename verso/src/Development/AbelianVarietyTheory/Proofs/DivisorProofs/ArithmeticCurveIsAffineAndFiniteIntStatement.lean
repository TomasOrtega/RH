import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticCurveIsAffineAndFiniteInt.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  first | exact @GlobalTheory.ArithCurve.isAffine_and_finite | exact GlobalTheory.ArithCurve.isAffine_and_finite | (intros; apply GlobalTheory.ArithCurve.isAffine_and_finite <;> assumption)
