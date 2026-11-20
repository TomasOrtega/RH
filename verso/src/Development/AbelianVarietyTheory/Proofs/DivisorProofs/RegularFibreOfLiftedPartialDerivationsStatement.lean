import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFibreOfLiftedPartialDerivations
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.regularFibre_of_liftedPartialDerivations` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRegularFibreOfLiftedPartialDerivations.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.regular_fibre_of_lifted_partialDerivations : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  first | exact @GlobalTheory.regularFibre_of_liftedPartialDerivations | exact GlobalTheory.regularFibre_of_liftedPartialDerivations | (intros; apply GlobalTheory.regularFibre_of_liftedPartialDerivations <;> assumption)
