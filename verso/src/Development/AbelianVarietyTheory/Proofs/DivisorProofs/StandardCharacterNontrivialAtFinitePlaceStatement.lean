import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterNontrivialAtFinitePlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsiLocNontriv.exists_psiLoc_ne_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStandardCharacterNontrivialAtFinitePlace.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.standard_character_nontrivial_at_finite_place : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1 := by
  first | exact @GlobalTheory.PsiLocNontriv.exists_psiLoc_ne_one | exact GlobalTheory.PsiLocNontriv.exists_psiLoc_ne_one | (intros; apply GlobalTheory.PsiLocNontriv.exists_psiLoc_ne_one <;> assumption)
