import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHaarMeasureUniqueSigmaCompactNormalisedCompactOp.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  first | exact @GlobalTheory.haar_unique_of_sigmaCompact_normalised | exact GlobalTheory.haar_unique_of_sigmaCompact_normalised | (intros; apply GlobalTheory.haar_unique_of_sigmaCompact_normalised <;> assumption)
