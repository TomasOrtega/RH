import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobenius
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsTwoPrimesSameNormOfTrivialFrobenius.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_two_primes_same_norm_of_trivial_frobenius : ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F] (σ : F ≃ₐ[K] F), σ ≠ 1 → ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 → ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one | exact GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one | (intros; apply GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one <;> assumption)
