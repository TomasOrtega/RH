import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntLevelSchwartzBruhatFiniteAdelic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIntLevelSchwartzBruhatFiniteAdelic.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_int_level_schwartzBruhat_finiteAdelic : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := by
  first | exact @GlobalTheory.SBLevel.exists_int_level | exact GlobalTheory.SBLevel.exists_int_level | (intros; apply GlobalTheory.SBLevel.exists_int_level <;> assumption)
