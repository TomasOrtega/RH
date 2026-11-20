import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemCoefRingInvertPrimeInvOfMemNeZero.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  first | exact @GlobalTheory.Ord2.memE_inv_of_mem | exact GlobalTheory.Ord2.memE_inv_of_mem | (intros; apply GlobalTheory.Ord2.memE_inv_of_mem <;> assumption)
