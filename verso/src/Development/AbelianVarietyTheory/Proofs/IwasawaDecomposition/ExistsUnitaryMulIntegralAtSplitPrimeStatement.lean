import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulIntegralAtSplitPrime
import Mathlib
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnIntApprox.exists_unitary_mul_integral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUnitaryMulIntegralAtSplitPrime.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.exists_unitary_mul_integral_at_split_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  first | exact @GlobalTheory.UnIntApprox.exists_unitary_mul_integral | exact GlobalTheory.UnIntApprox.exists_unitary_mul_integral | (intros; apply GlobalTheory.UnIntApprox.exists_unitary_mul_integral <;> assumption)
