import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleClearDenominator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteAdeleClearDenominator.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_adele_clear_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ a : Af E, ∃ m : E, m ≠ 0 ∧ algebraMap E (Af E) m * a ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO | exact GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO | (intros; apply GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO <;> assumption)
