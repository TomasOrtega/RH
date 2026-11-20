import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_local_basis_of_isLattice` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalBasisAtPrimeOfIsLattice.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_localBasis_at_prime_of_isLattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E → ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧ ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  first | exact @GlobalTheory.exists_local_basis_of_isLattice | exact GlobalTheory.exists_local_basis_of_isLattice | (intros; apply GlobalTheory.exists_local_basis_of_isLattice <;> assumption)
