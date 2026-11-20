import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproximationModConductor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteAdeleApproximationModConductor.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finite_adele_approximation_mod_conductor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (y : (Af E)ˣ) (z : Af E), ∃ x : E, (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO | exact GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO | (intros; apply GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO <;> assumption)
