import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolynomialFieldExtensionDegree
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPolynomialFieldExtensionDegree.lean&line=4#L4)
-/
theorem _root_.GlobalTheory.T.polynomial_field_extension_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  first | exact @GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree | exact GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree <;> assumption)
