import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsWeaklyRegularMvPowerSeriesOfFiniteColength
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | exact GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | (intros; apply GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ Ideal.span (Set.range f)) → RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  first | exact @GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | exact GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | (intros; apply GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le <;> assumption)
