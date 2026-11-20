import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTranspose
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.ss_tpow_transpose` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FCompletelyReducibleKroneckerPowerTranspose.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.completelyReducible_kroneckerPower_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_tpow_transpose | exact GlobalTheory.ClassFin.ss_tpow_transpose | (intros; apply GlobalTheory.ClassFin.ss_tpow_transpose <;> assumption)
