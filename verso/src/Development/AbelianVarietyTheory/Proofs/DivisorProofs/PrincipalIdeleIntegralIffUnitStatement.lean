import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalIdeleIntegralIffUnit
import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RatIdInt.ratId_mem_intU_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalIdeleIntegralIffUnit.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.principal_idele_integral_iff_unit : ∀ (L : Type) [Field L] [NumberField L] (a : Lˣ),
    ratId ℚ L a ∈ intU ℚ L ↔ IsIntegral ℤ (a : L) ∧ IsIntegral ℤ ((a⁻¹ : Lˣ) : L) := by
  first | exact @GlobalTheory.RatIdInt.ratId_mem_intU_iff | exact GlobalTheory.RatIdInt.ratId_mem_intU_iff | (intros; apply GlobalTheory.RatIdInt.ratId_mem_intU_iff <;> assumption)
