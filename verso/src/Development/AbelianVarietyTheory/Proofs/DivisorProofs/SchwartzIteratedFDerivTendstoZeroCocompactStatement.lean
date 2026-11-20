import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIteratedFDerivTendstoZeroCocompact
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzIteratedFDerivTendstoZeroCocompact.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.schwartz_iteratedFDeriv_tendsto_zero_cocompact' : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ), Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by
  first | exact @GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact | exact GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact | (intros; apply GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact <;> assumption)
