import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructure
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFixedFieldStructure.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.fixed_field_structure : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  first | exact @GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | exact GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | (intros; apply GlobalTheory.CompanionTheory.FixedPointsCM.fixedK <;> assumption)
