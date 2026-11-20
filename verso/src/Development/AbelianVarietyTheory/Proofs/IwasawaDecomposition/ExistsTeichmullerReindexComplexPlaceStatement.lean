import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TeichAt.exists_teich_reindex` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsTeichmullerReindexComplexPlace.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.exists_teichmuller_reindex_complexPlace : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ, Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  first | exact @GlobalTheory.TeichAt.exists_teich_reindex | exact GlobalTheory.TeichAt.exists_teich_reindex | (intros; apply GlobalTheory.TeichAt.exists_teich_reindex <;> assumption)
