import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TiltFacts.obFacts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegralRingFacts.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.integral_ring_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  first | exact @GlobalTheory.CompanionTheory.TiltFacts.obFacts | exact GlobalTheory.CompanionTheory.TiltFacts.obFacts | (intros; apply GlobalTheory.CompanionTheory.TiltFacts.obFacts <;> assumption)
