import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFactsStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

/- English proof (translation)
The claim follows from `GlobalTheory.T.integral_ring_facts`.
-/
theorem CrystallineSemistableComparison.RL.d_ob : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := GlobalTheory.T.integral_ring_facts

/- English proof (translation)
The claim follows from `GlobalTheory.T.acris_level_one_facts`.
-/
theorem CrystallineSemistableComparison.RL.acris_mod_l_base_change : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := GlobalTheory.T.acris_level_one_facts

/- English proof (translation)
The claim follows from `GlobalTheory.T.acris_level_sequence_facts`.
-/
theorem CrystallineSemistableComparison.RL.d_seq : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := GlobalTheory.T.acris_level_sequence_facts
