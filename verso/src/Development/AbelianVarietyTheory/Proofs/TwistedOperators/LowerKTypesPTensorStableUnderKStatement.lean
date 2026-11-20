import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLowerKTypesPTensorStableUnderK.lean&line=267#L267)
-/
theorem _root_.GlobalTheory.T.lowerKTypes_pTensor_stable_under_K : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), LowData ε E Λ u j → IsTau ε Λ τ w → TauTie ε E j τ → ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ k ∈ Kset ε, ∃ G' : Fin n × Fin n → W, arr1 j G' ∈ Vminus ε E Λ u ∧ ∑ p, ⟪τ k w, G p⟫_ℂ • (k⁻¹ * thE ε p * k) = ∑ p, ⟪w, G' p⟫_ℂ • thE ε p := by
  first | exact @GlobalTheory.SphJet.vminus_stable_under_K | exact GlobalTheory.SphJet.vminus_stable_under_K | (intros; apply GlobalTheory.SphJet.vminus_stable_under_K <;> assumption)
