import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCongruenceSubgroupCosetDecomposition.lean&line=390#L390)
-/
theorem _root_.GlobalTheory.T.congruence_subgroup_coset_decomposition : Ad3.R.C1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinStepC.c1 | exact GlobalTheory.CompanionTheory.RankinStepC.c1 | (intros; apply GlobalTheory.CompanionTheory.RankinStepC.c1 <;> assumption)
