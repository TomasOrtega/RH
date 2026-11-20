import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSeriesRingHomExtendingFiniteFree

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.powerSeries_extend_finite_free` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsPowerSeriesRingHomExtendingFiniteFree.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free : ∀ (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) → ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = i PowerSeries.X ∧ ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first | exact @GlobalTheory.powerSeries_extend_finite_free | exact GlobalTheory.powerSeries_extend_finite_free | (intros; apply GlobalTheory.powerSeries_extend_finite_free <;> assumption)
