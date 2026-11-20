import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHolomorphicLowestKTypeComplexified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphJet.LowTau.exists_tau` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsHolomorphicLowestKTypeComplexified.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_holomorphic_lowestKType_complexified : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) (u : V), IsURepOn (UJset ε) σ → DerTie ε σ E ι → ‖u‖ = 1 → IsKTypeOf ε σ Λ ((kSpan ε E u).map ι.toLinearMap) → IsWtOn (Kset ε) σ Λ (ι u) → ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (j : W →ₗᵢ[ℂ] V), IsTau ε Λ τ w ∧ j w = u ∧ LinearMap.range j.toLinearMap = kSpan ε E u ∧ TauTie ε E j τ := by
  first | exact @GlobalTheory.SphJet.LowTau.exists_tau | exact GlobalTheory.SphJet.LowTau.exists_tau | (intros; apply GlobalTheory.SphJet.LowTau.exists_tau <;> assumption)
