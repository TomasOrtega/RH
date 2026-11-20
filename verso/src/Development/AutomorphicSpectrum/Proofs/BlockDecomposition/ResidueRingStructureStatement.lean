import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FResidueRingStructure.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.residue_ring_structure : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  first | exact @GlobalTheory.CompanionTheory.RvRingPf.rvRing | exact GlobalTheory.CompanionTheory.RvRingPf.rvRing | (intros; apply GlobalTheory.CompanionTheory.RvRingPf.rvRing <;> assumption)
