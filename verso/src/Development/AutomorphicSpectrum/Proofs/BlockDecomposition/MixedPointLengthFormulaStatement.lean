import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMixedPointLengthFormula.lean&line=303#L303)
-/
theorem _root_.GlobalTheory.T.mixed_point_length_formula : GlobalTheory.CompanionTheory.MixZ.PtLen := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | exact GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | (intros; apply GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen <;> assumption)
