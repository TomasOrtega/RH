import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorIntegralCompletion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
open NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EigenDivide.exists_projection_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEigenvectorIntegralCompletion.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.eigenvector_integral_completion : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (F : Type) [Field F] [CharZero F] (R : Subring F)
    (N : ℕ) (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) (τ : E →+* F) (y : Fin N → F), (∀ i, y i ∈ R) →
    (∀ a : 𝓞 E, ((ρ a).map (Int.castRingHom F)).mulVec y = τ (a : E) • y) →
    ∀ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → F, (∀ k, r k ∈ R) →
    ∃ z : Fin N → F, (∀ i, z i ∈ R) ∧ ∀ P : Matrix (Fin N) (Fin N) F,
      (∀ a : 𝓞 E, P * (ρ a).map (Int.castRingHom F) = τ (a : E) • P) →
      P.mulVec z = (∑ k, r k * τ ((integralBasis E).traceDual k)) • P.mulVec y := by
  first | exact @GlobalTheory.EigenDivide.exists_projection_eq | exact GlobalTheory.EigenDivide.exists_projection_eq | (intros; apply GlobalTheory.EigenDivide.exists_projection_eq <;> assumption)
