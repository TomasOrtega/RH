import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityGenericUnitary
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.pair_multiplicity_generic_unitary : GlobalTheory.CompanionTheory.PairMult.GenCOU2 := by
  first | exact @GlobalTheory.CompanionTheory.PairMult.COU.genCOU2 | exact GlobalTheory.CompanionTheory.PairMult.COU.genCOU2 | (intros; apply GlobalTheory.CompanionTheory.PairMult.COU.genCOU2 <;> assumption)
