import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLower
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCentralTorusContractsLower.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.central_torus_contracts_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | exact GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract <;> assumption)
