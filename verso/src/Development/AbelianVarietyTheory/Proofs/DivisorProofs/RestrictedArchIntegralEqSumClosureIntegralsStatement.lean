import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchIntegralEqSumClosureIntegrals
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixHt.resArch_eq_finsum_cycInt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRestrictedArchIntegralEqSumClosureIntegrals.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  first | exact @GlobalTheory.MixHt.resArch_eq_finsum_cycInt | exact GlobalTheory.MixHt.resArch_eq_finsum_cycInt | (intros; apply GlobalTheory.MixHt.resArch_eq_finsum_cycInt <;> assumption)
