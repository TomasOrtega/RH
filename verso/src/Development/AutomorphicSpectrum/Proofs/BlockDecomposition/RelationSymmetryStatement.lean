import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationSymmetry
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RelSym.relSymm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelationSymmetry.lean&line=596#L596)
-/
theorem _root_.GlobalTheory.T.relation_symmetry : RelSymm := by
  first | exact @GlobalTheory.CompanionTheory.RelSym.relSymm | exact GlobalTheory.CompanionTheory.RelSym.relSymm | (intros; apply GlobalTheory.CompanionTheory.RelSym.relSymm <;> assumption)
