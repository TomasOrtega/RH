import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEtaleMvPolynomialHypersurface
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.standardEtale_mvPolynomial_hypersurface` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStandardEtaleMvPolynomialHypersurface.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.standardEtale_localization_away_quotient_span : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  first | exact @GlobalTheory.standardEtale_mvPolynomial_hypersurface | exact GlobalTheory.standardEtale_mvPolynomial_hypersurface | (intros; apply GlobalTheory.standardEtale_mvPolynomial_hypersurface <;> assumption)
