import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChainLeIInfSupPowSmulTopOfPrecomplete
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.chain_le_iInf_sup_pow_smul_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FChainLeIInfSupPowSmulTopOfPrecomplete.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete : ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ) (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  first | exact @GlobalTheory.chain_le_iInf_sup_pow_smul_top | exact GlobalTheory.chain_le_iInf_sup_pow_smul_top | (intros; apply GlobalTheory.chain_le_iInf_sup_pow_smul_top <;> assumption)
