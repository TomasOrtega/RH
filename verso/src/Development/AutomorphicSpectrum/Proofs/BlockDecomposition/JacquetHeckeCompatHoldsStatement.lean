import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeCompatHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetHeckeCompatHolds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.jacquet_hecke_compat_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat | exact GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat | (intros; apply GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat <;> assumption)
