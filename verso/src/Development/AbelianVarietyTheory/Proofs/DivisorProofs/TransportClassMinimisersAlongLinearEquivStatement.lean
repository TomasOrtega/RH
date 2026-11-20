import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.transport_minimisers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTransportClassMinimisersAlongLinearEquiv.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.transport_classMinimisers_along_linearEquiv : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  first | exact @GlobalTheory.transport_minimisers | exact GlobalTheory.transport_minimisers | (intros; apply GlobalTheory.transport_minimisers <;> assumption)
