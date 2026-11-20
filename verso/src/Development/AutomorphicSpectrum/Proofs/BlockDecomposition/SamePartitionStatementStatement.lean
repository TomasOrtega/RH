import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SamePartitionStatement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSamePartitionStatement.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.same_partition_statement : ReciprocityTheory.Ty.Fin.St.SamePart := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSamePart.samePart | exact GlobalTheory.CompanionTheory.TyFinSamePart.samePart | (intros; apply GlobalTheory.CompanionTheory.TyFinSamePart.samePart <;> assumption)
