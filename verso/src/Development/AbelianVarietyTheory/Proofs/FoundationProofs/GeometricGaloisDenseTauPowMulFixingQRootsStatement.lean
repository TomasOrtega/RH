import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisDenseTauPowMulFixingQRoots
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.Dense.dense_tau_pow_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGeometricGaloisDenseTauPowMulFixingQRoots.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.geometricGalois_dense_tau_pow_mul_fixing_qRoots : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ g ∈ Ggeo p Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ x ∈ S, (τ ^ s * h) x = g x := by
  first | exact @GlobalTheory.K5.Dense.dense_tau_pow_mul | exact GlobalTheory.K5.Dense.dense_tau_pow_mul | (intros; apply GlobalTheory.K5.Dense.dense_tau_pow_mul <;> assumption)
