import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMono
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStandardBlocksReindexStrictMono.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.standard_blocks_reindex_strictMono : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))), stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  first | exact @GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty | exact GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty | (intros; apply GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty <;> assumption)
