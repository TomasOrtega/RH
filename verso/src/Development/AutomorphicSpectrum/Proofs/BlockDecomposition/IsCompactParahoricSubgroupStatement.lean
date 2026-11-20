import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroup
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsCompactParahoricSubgroup.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isCompact_parahoric_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx | exact GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx <;> assumption)
