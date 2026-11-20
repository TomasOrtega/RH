import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FExistsUniformizerNonarchimedean.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_uniformizer_nonarchimedean : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L], ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_isUnif | exact GlobalTheory.CompanionTheory.CartGL.exists_isUnif | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_isUnif <;> assumption)
