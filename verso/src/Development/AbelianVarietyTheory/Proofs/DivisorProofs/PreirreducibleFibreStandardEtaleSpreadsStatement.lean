import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleFibreStandardEtaleSpreads
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPreirreducibleFibreStandardEtaleSpreads.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.preirreducible_fibre_standardEtale_spreads : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  first | exact @GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads | exact GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads | (intros; apply GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads <;> assumption)
