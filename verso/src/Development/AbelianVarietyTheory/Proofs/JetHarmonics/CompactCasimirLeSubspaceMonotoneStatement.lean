import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeSubspaceMonotone
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.casKLe_subspace_mono` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCompactCasimirLeSubspaceMonotone.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.compactCasimirLe_subspace_monotone : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → (∀ c, CasKLe ε E c 0) ∧ (∀ c x y, CasKLe ε E c x → CasKLe ε E c y → CasKLe ε E c (x + y)) ∧ (∀ c (a : ℂ) x, CasKLe ε E c x → CasKLe ε E c (a • x)) ∧ ∀ c c' x, 0 ≤ c → c ≤ c' → CasKLe ε E c x → CasKLe ε E c' x := by
  first | exact @GlobalTheory.casKLe_subspace_mono | exact GlobalTheory.casKLe_subspace_mono | (intros; apply GlobalTheory.casKLe_subspace_mono <;> assumption)
