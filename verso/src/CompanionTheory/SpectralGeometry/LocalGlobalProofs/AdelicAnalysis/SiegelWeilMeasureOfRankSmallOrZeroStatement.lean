import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfRankSmallOrZero
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FSiegelWeilMeasureOfRankSmallOrZero.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all | exact GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all | (intros; apply GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all <;> assumption)
