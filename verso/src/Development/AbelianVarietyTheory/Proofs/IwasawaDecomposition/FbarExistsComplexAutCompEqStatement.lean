import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFbarExistsComplexAutCompEq.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.fbar_exists_complexAut_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  first | exact @GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | exact GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | (intros; apply GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq <;> assumption)
