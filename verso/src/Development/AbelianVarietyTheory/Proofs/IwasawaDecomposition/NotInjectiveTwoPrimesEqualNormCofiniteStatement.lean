import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.ZetaPole.not_injective_double_primes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNotInjectiveTwoPrimesEqualNormCofinite.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.not_injective_two_primes_equal_norm_cofinite : ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  first | exact @GlobalTheory.Mem.ZetaPole.not_injective_double_primes | exact GlobalTheory.Mem.ZetaPole.not_injective_double_primes | (intros; apply GlobalTheory.Mem.ZetaPole.not_injective_double_primes <;> assumption)
