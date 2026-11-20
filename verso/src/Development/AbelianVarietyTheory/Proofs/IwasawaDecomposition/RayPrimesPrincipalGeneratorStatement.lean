import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimesPrincipalGenerator
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRayPrimesPrincipalGenerator.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.ray_primes_principal_generator : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → ∀ (X : ℝ), ∀ v ∈ rayPrimes 𝔮 X, ∃ π : 𝓞 K, v.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  first | exact @GlobalTheory.Mem.An.exists_generator_of_mem_rayPrimes | exact GlobalTheory.Mem.An.exists_generator_of_mem_rayPrimes | (intros; apply GlobalTheory.Mem.An.exists_generator_of_mem_rayPrimes <;> assumption)
