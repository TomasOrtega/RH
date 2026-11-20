import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomPowerSeriesRoot

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ringHom_powerSeries_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsRingHomPowerSeriesRoot.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.exists_ringHom_powerSeries_root' : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  first | exact @GlobalTheory.exists_ringHom_powerSeries_root | exact GlobalTheory.exists_ringHom_powerSeries_root | (intros; apply GlobalTheory.exists_ringHom_powerSeries_root <;> assumption)
