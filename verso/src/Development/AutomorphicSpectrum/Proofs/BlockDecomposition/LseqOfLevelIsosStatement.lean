import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TowerSeq.lseq_transport` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLseqOfLevelIsos.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.lseq_of_level_isos : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W) (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)), (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) → LSeq l S S' → Nonempty (LSeq l T T') := by
  first | exact @GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | exact GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | (intros; apply GlobalTheory.CompanionTheory.TowerSeq.lseq_transport <;> assumption)
