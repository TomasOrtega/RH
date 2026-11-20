import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
import Mathlib
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDualWeylLatticeExistsNatPowSmulMem.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsLattice E M → Submodule.IsLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem | exact GlobalTheory.NabScale.nabAtr_smul_pow_mem | (intros; apply GlobalTheory.NabScale.nabAtr_smul_pow_mem <;> assumption)
