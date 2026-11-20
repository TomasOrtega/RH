import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviSubspaceInvariantUnderBlocks
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgTransport.leviSub_stable` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLeviSubspaceInvariantUnderBlocks.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.levi_subspace_invariant_under_blocks : ∀ {n : ℕ} (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3) (a b : Fin n), blk (stdBlocks d h) a = blk (stdBlocks d h) b → ∀ x ∈ leviSub P d h χ L, P.E a b x ∈ leviSub P d h χ L := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | exact GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | (intros; apply GlobalTheory.CompanionTheory.RgTransport.leviSub_stable <;> assumption)
