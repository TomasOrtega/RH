import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverDegreeOmega
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRegularCoverDegreeOmega.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.regular_cover_degree_omega : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ (P : PPAS X) (C : RegCover p) (P' : PPAS C.Y) (φ : P'.A.left ⟶ P.A.left), P'.IsPull P C.ρ φ → P'.degOmega (C.ρ ≫ p) = C.deg * P.degOmega p ∧ ∀ a : ℝ, P'.IsCh2Omega (C.ρ ≫ p) a → P.IsCh2Omega p (a / C.deg) := by
  first | exact @GlobalTheory.CoverHodge.degOmega_ch2Omega_cover | exact GlobalTheory.CoverHodge.degOmega_ch2Omega_cover | (intros; apply GlobalTheory.CoverHodge.degOmega_ch2Omega_cover <;> assumption)
