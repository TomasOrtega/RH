import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsNiceLocalFieldProductRingInfiniteAdelesComplet.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions : ∀ (F : Type) [Field F] [NumberField F], Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  first | exact @GlobalTheory.GaugeEx.nice_ainf_fv | exact GlobalTheory.GaugeEx.nice_ainf_fv | (intros; apply GlobalTheory.GaugeEx.nice_ainf_fv <;> assumption)
