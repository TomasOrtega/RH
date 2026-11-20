import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorLinearDescentPointOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.LinDesc.omega_pt_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisTransferFactorLinearDescentPointOne.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.jacquetRallisTransferFactor_linearDescentPoint_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  first | exact @GlobalTheory.JR.LinDesc.omega_pt_one | exact GlobalTheory.JR.LinDesc.omega_pt_one | (intros; apply GlobalTheory.JR.LinDesc.omega_pt_one <;> assumption)
