import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecomposition
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FAdeleHaarProductDecomposition.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.adele_haar_product_decomposition : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)), m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod <;> assumption)
