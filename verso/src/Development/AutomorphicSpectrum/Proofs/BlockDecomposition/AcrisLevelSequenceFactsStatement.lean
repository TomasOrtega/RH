import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAcrisLevelSequenceFacts.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.acris_level_sequence_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := by
  first | exact @GlobalTheory.CompanionTheory.LSeq.racrSeq | exact GlobalTheory.CompanionTheory.LSeq.racrSeq | (intros; apply GlobalTheory.CompanionTheory.LSeq.racrSeq <;> assumption)
