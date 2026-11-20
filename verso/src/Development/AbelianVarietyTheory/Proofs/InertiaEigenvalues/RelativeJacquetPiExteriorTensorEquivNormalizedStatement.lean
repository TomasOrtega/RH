import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JacStages.relJacD_piTensor_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRelativeJacquetPiExteriorTensorEquivNormalized.lean&line=221#L221)
-/
theorem _root_.GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  first | exact @GlobalTheory.JacStages.relJacD_piTensor_equiv | exact GlobalTheory.JacStages.relJacD_piTensor_equiv | (intros; apply GlobalTheory.JacStages.relJacD_piTensor_equiv <;> assumption)
