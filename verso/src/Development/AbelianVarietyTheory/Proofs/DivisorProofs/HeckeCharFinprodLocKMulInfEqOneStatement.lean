import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCharUnit.finprod_locK_mul_inf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeCharFinprodLocKMulInfEqOne.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ), (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  first | exact @GlobalTheory.HCharUnit.finprod_locK_mul_inf | exact GlobalTheory.HCharUnit.finprod_locK_mul_inf | (intros; apply GlobalTheory.HCharUnit.finprod_locK_mul_inf <;> assumption)
