import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEq
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FSumOfLevelSizesEq.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.sum_of_level_sizes_eq : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card | exact GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card <;> assumption)
