import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriLeviUnipotentFactor
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KOneFactor.kone_factor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwahoriLeviUnipotentFactor.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.iwahori_levi_unipotent_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.KOneFactor.kone_factor | exact GlobalTheory.CompanionTheory.KOneFactor.kone_factor | (intros; apply GlobalTheory.CompanionTheory.KOneFactor.kone_factor <;> assumption)
