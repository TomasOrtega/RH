import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacter
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarMeasureIwasawaModularCharacter.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.haar_measure_iwasawa_modular_character : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | exact GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | (intros; apply GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law <;> assumption)
