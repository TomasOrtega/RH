import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNormalMvPolynomialOfIsNormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsNormalMvPolynomialOfIsNormal.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isNormal_mvPolynomial_of_isNormal : ∀ (R : Type) [CommRing R] (r : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial (Fin r) R)) := by
  first | exact @GlobalTheory.isNormalScheme_sp_mvPolynomial | exact GlobalTheory.isNormalScheme_sp_mvPolynomial | (intros; apply GlobalTheory.isNormalScheme_sp_mvPolynomial <;> assumption)
