import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSer.exists_acris_Lam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAcrisPhiPowEigenvectorDoubleSeries.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.exists_acris_Lam | exact GlobalTheory.PSer.exists_acris_Lam | (intros; apply GlobalTheory.PSer.exists_acris_Lam <;> assumption)
