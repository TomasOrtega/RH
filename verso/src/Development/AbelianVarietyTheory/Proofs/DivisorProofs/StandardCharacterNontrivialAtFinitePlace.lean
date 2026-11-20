import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis

namespace GlobalTheory.PsiLocNontriv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_psiLoc_ne_one : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1 := by
  intro F _ _ ψ hψ v
  by_contra h
  push Not at h
  refine GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v (AddChar.ext _ _ fun t => ?_)
  rw [AddChar.one_apply]
  exact h t

end GlobalTheory.PsiLocNontriv
