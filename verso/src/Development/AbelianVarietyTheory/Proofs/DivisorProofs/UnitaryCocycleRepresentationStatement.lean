import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCocycleRepresentation
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryCocycleRepresentation.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.unitary_cocycle_representation : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), (1 : G) ∈ K → (∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) → (∀ k ∈ K, k⁻¹ ∈ K) → LinearIndependent ℂ b → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → A 1 = 1 ∧ (∀ k ∈ K, ∀ k' ∈ K, A (k * k') = A k * A k') ∧ ∀ k ∈ K, A k⁻¹ = star (A k) := by
  first | exact @GlobalTheory.matrices_unitary_hom_of_linearIndependent | exact GlobalTheory.matrices_unitary_hom_of_linearIndependent | (intros; apply GlobalTheory.matrices_unitary_hom_of_linearIndependent <;> assumption)
