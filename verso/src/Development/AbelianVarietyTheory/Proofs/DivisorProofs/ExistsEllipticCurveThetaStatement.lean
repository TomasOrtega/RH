import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticCurveTheta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ppas_g_one_hasTheta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEllipticCurveTheta.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_elliptic_curve_theta : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (E : PPAS (Sp (𝓞 K))), E.g = 1 ∧ E.HasTheta := by
  first | exact @GlobalTheory.exists_ppas_g_one_hasTheta | exact GlobalTheory.exists_ppas_g_one_hasTheta | (intros; apply GlobalTheory.exists_ppas_g_one_hasTheta <;> assumption)
