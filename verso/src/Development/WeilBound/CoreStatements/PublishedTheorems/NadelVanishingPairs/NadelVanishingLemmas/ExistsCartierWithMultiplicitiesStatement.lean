import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPublishedTheorems%2FNadelVanishingPairs%2FNadelVanishingLemmas%2FExistsCartierWithMultiplicities.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.exists_cartier_with_multiplicities : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ, (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) → ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  first | exact @_root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | exact _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | (intros; apply _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial <;> assumption)
