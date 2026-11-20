import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification

namespace GlobalTheory.DvrCompletion

/- English proof (translation)
Introduce `A _ _ _ _`. Take `⟨V, _, _, _, ι, h, h1, h2⟩` from `GlobalTheory.Mum.exists_cDvr_injective_isLocalHom A`. Conclude with `⟨V, inferInstance, inferInstance, inferInstance, h, ι, h1, h2⟩`.
-/
theorem exists_cDvr_of_isDiscreteValuationRing : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ ι : A →+* V, Function.Injective ι ∧ IsLocalHom ι := by
  intro A _ _ _ _
  obtain ⟨V, _, _, _, ι, h, h1, h2⟩ := GlobalTheory.Mum.exists_cDvr_injective_isLocalHom A
  exact ⟨V, inferInstance, inferInstance, inferInstance, h, ι, h1, h2⟩

end GlobalTheory.DvrCompletion
