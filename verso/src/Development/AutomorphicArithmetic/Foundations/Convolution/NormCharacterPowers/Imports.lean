import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open UpperTheory.ConvolutionTheory.R

open NumberField in
/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)`.
-/
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

/- English proof (translation)
Introduce `H K M _ _ _ _ _ _ hK hM hp n hn π P hbc`. Break down `π with @⟨_, π⟩ | @⟨hR, π⟩` into its components or cases. Use `swap`. Conclude with `(not_both K hR hK).elim`. Break down `P with @⟨_, P⟩ | @⟨hR, P⟩` into its components or cases.

Use `swap`. Conclude with `(not_both M hR hM).elim`. Take `⟨h1, h2⟩` from `H K M hp n (GlobalTheory.CuspRep.CG.mk π) (GlobalTheory.CuspRep.CG.mk P) hn hbc`. Use `⟨fun η hη hi => h1 η hη (Quotient.sound hi), fun π₁ hbc₁ => ?_⟩` and prove the remaining obligations. Break down `π₁ with @⟨_, π₁⟩ | @⟨hR, π₁⟩` into its components or cases.

Use `swap`. Conclude with `(not_both K hR hK).elim`. Take `⟨η, hη, e⟩` from `h2 (GlobalTheory.CuspRep.CG.mk π₁) hbc₁`. Conclude with `⟨η, hη, Quotient.exact e⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R.fibre :
    FibreCG → Fibre := by
  intro H K M _ _ _ _ _ _ hK hM hp n hn π P hbc
  rcases π with @⟨_, π⟩ | @⟨hR, π⟩
  swap
  · exact (not_both K hR hK).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR hM).elim
  obtain ⟨h1, h2⟩ := H K M hp n (GlobalTheory.CuspRep.CG.mk π) (GlobalTheory.CuspRep.CG.mk P) hn hbc
  refine ⟨fun η hη hi => h1 η hη (Quotient.sound hi), fun π₁ hbc₁ => ?_⟩
  rcases π₁ with @⟨_, π₁⟩ | @⟨hR, π₁⟩
  swap
  · exact (not_both K hR hK).elim
  obtain ⟨η, hη, e⟩ := h2 (GlobalTheory.CuspRep.CG.mk π₁) hbc₁
  exact ⟨η, hη, Quotient.exact e⟩
