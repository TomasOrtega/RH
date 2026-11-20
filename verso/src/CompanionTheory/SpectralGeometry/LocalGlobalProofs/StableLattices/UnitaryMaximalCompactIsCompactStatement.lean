import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryMaximalCompactIsCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FUnitaryMaximalCompactIsCompact.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.unitary_maximal_compact_is_compact : ∀ (n : ℕ) (ε : Fin n → Bool), IsCompact ((S7.KG ε : Subgroup (S7.UJ ε)) : Set (S7.UJ ε)) := by
  first | exact @GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set | exact GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set | (intros; apply GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set <;> assumption)
