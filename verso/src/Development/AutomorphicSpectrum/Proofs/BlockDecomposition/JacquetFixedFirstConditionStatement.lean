import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstCondition
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetFixedFirstCondition.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.jacquet_fixed_first_condition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | exact GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | (intros; apply GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul <;> assumption)
