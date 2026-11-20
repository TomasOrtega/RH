import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNeg
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
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDvrPlaceDiscKaehlerWedgePermNeg.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K) (σ : Equiv.Perm (Fin n))
  (E : Place c) (φ : K →₀ ℚ), E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  first | exact @GlobalTheory.FieldPair.disc_dForm_perm_neg | exact GlobalTheory.FieldPair.disc_dForm_perm_neg | (intros; apply GlobalTheory.FieldPair.disc_dForm_perm_neg <;> assumption)
