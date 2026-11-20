import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCartanInvolutionHyperbolicSwapExtension.lean&line=211#L211)
-/
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), M.conjTranspose = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y = Complex.I →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    IsCartan (ιᵀ * M * ι.map star) θ₁ →
    ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ ∃ c : ℂ, c ≠ 0 ∧ Y = c • θ *ᵥ X := by
  first | exact @GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | exact GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | (intros; apply GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap <;> assumption)
