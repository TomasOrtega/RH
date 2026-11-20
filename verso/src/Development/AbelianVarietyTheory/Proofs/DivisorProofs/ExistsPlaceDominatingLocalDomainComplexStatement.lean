import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplex
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPlaceDominatingLocalDomainComplex.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_place_dominating_local_domain_complex : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hO : IsLocModel (algebraMap ℂ κ) O), letI := hO.isLocalRing;
  ¬ IsField O → ∃ F : Place (algebraMap ℂ κ), F.Contains O ∧ ∀ f : O, f ∈ IsLocalRing.maximalIdeal O → (f : κ) ≠ 0 → 0 < F.ord f := by
  first | exact @GlobalTheory.DvrDom.exists_place_dominating | exact GlobalTheory.DvrDom.exists_place_dominating | (intros; apply GlobalTheory.DvrDom.exists_place_dominating <;> assumption)
