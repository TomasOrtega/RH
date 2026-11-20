import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeConditionHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetHeckeConditionHolds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.jacquet_hecke_condition_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  first | exact @GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | exact GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | (intros; apply GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp <;> assumption)
