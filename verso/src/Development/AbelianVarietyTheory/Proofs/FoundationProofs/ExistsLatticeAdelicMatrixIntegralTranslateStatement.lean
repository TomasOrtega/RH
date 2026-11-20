import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdelicMatLat.exists_lattice_integral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLatticeAdelicMatrixIntegralTranslate.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.exists_lattice_adelicMatrix_integral_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  first | exact @GlobalTheory.AdelicMatLat.exists_lattice_integral | exact GlobalTheory.AdelicMatLat.exists_lattice_integral | (intros; apply GlobalTheory.AdelicMatLat.exists_lattice_integral <;> assumption)
