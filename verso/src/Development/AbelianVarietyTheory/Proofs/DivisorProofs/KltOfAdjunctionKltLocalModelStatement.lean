import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKltOfAdjunctionKltLocalModel.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.klt_of_adjunctionKlt_localModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L) (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T → IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 → S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ → AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  first | exact @GlobalTheory.FieldPair.klt_of_adjKlt_locModel | exact GlobalTheory.FieldPair.klt_of_adjKlt_locModel | (intros; apply GlobalTheory.FieldPair.klt_of_adjKlt_locModel <;> assumption)
