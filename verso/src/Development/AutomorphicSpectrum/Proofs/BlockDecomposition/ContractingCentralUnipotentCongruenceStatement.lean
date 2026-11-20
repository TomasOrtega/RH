import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruence
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZjContract.zj_contract` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContractingCentralUnipotentCongruence.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.contracting_central_unipotent_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ZjContract.zj_contract | exact GlobalTheory.CompanionTheory.ZjContract.zj_contract | (intros; apply GlobalTheory.CompanionTheory.ZjContract.zj_contract <;> assumption)
