import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FArithmeticVarietyDimZeroFinite.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.arithmetic_variety_dim_zero_finite : ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) (q : Z ⟶ Sp k), IsArithVar q 0 → IsFinite q := by
  first | exact @GlobalTheory.ArithCurveFinite.isFinite | exact GlobalTheory.ArithCurveFinite.isFinite | (intros; apply GlobalTheory.ArithCurveFinite.isFinite <;> assumption)
