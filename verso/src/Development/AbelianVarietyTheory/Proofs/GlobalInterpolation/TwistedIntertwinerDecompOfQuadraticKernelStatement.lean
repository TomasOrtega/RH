import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernel
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTwistedIntertwinerDecompOfQuadraticKernel.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (σ σ' : Γ →* GL (Fin n) k) (S : Subgroup Γ) (χ η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k), (∀ g ∈ S, η g = 1 → ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₁ = ((χ g : ℤ) : k) • (X₁ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₂ = (((χ * η) g : ℤ) : k) • (X₂ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) := by
  first | exact @GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel | exact GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel | (intros; apply GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel <;> assumption)
