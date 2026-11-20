import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FHermitianCharacters%2FSelfDualLatticeFiltrationCharacter.lean&line=366#L366)
-/
theorem _root_.GlobalTheory.T.adelic_character_local_nontrivial : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiV F ψ v) ∧ ∃ y, psiV F ψ v y ≠ 1) ∧ Continuous (psiInf F ψ) ∧ ∀ (w : InfinitePlace F), ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place | exact GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place | (intros; apply GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place <;> assumption)
