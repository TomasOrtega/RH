import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EsymmVirt.esymm_mem_virt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEsymmMemVirtualCharactersOfPowerSumEigenvalues.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ), φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) → ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.EsymmVirt.esymm_mem_virt | exact GlobalTheory.EsymmVirt.esymm_mem_virt | (intros; apply GlobalTheory.EsymmVirt.esymm_mem_virt <;> assumption)
