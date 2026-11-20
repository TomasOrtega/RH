import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.red_subst` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIntegralReducingToMvPowerSeriesSubst.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k), (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) → (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧ ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c → subst u f ∈ intBy p k τ c := by
  first | exact @GlobalTheory.Katz.red_subst | exact GlobalTheory.Katz.red_subst | (intros; apply GlobalTheory.Katz.red_subst <;> assumption)
