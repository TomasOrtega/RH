import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirrorPartitions
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.Mirrors.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirrorPartitions.lean&line=216#L216)
-/
theorem _root_.GlobalTheory.T.mirror_partitions : ReciprocityTheory.Ty.Fin.St.MirrorsOf := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Mirrors.main | exact GlobalTheory.CompanionTheory.TyFin.Mirrors.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.Mirrors.main <;> assumption)
