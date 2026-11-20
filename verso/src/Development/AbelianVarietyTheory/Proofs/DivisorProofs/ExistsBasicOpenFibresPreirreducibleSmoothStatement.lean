import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBasicOpenFibresPreirreducibleSmooth.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B → ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) → PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧ (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → IsPreirreducible {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  first | exact @GlobalTheory.exists_basicOpen_fibres_preirreducible | exact GlobalTheory.exists_basicOpen_fibres_preirreducible | (intros; apply GlobalTheory.exists_basicOpen_fibres_preirreducible <;> assumption)
