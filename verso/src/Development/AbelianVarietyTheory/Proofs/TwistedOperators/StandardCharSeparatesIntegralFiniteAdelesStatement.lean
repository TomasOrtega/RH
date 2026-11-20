import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharSeparatesIntegralFiniteAdeles
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdCharSep.exists_sep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FStandardCharSeparatesIntegralFiniteAdeles.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.standardChar_separates_integralFiniteAdeles : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := by
  first | exact @GlobalTheory.StdCharSep.exists_sep | exact GlobalTheory.StdCharSep.exists_sep | (intros; apply GlobalTheory.StdCharSep.exists_sep <;> assumption)
