import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRepApply
open GlobalTheory.JR GlobalTheory.JR.WeilProd
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsLocallyConstantTestRepresentationTensorProduct.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  first | exact @GlobalTheory.JR.WeilProd.isTestRep_tensorRep | exact GlobalTheory.JR.WeilProd.isTestRep_tensorRep | (intros; apply GlobalTheory.JR.WeilProd.isTestRep_tensorRep <;> assumption)
