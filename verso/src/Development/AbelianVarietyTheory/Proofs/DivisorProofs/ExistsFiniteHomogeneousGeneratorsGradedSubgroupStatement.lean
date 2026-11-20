import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteHomogeneousGeneratorsGradedSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteHomogeneousGeneratorsGradedSubgroup.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_finite_homogeneous_generators_graded_subgroup : ∀ (K : Type) [CommRing K] (D c : ℕ) (x : Fin (D + 1) → K) (ι : Type) [Fintype ι] (w : ι → K) (Λ : ℕ → AddSubgroup K), (∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1)) → (∀ q, ∀ f ∈ Λ q, ∃ T : ι → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, aeval x (T i) * w i) → ∃ G : Finset (ℕ × K), (∀ g ∈ G, g.2 ∈ Λ g.1) ∧ ∀ q, Λ q ≤ AddSubgroup.closure {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} := by
  first | exact @GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators | exact GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators | (intros; apply GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators <;> assumption)
