import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaugeEx.exists_isProd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsIsRestrictedProductTupleMeasure.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_isRestrictedProductTupleMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), Conv b mi mv → ∃ ν, IsProd b ν mi mv := by
  first | exact @GlobalTheory.GaugeEx.exists_isProd | exact GlobalTheory.GaugeEx.exists_isProd | (intros; apply GlobalTheory.GaugeEx.exists_isProd <;> assumption)
