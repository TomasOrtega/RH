import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaugeEx.CharLoc.char_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLocalComponentsNontrivialAdelicCharacter.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.localComponents_nontrivial_adelic_character : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  first | exact @GlobalTheory.GaugeEx.CharLoc.char_local | exact GlobalTheory.GaugeEx.CharLoc.char_local | (intros; apply GlobalTheory.GaugeEx.CharLoc.char_local <;> assumption)
