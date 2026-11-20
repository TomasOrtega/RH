import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEventuallyDefiniteUnitaryLocalPointMemMaxCompact.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodInt.locPt_mem_KL | exact GlobalTheory.BCT.GoodInt.locPt_mem_KL | (intros; apply GlobalTheory.BCT.GoodInt.locPt_mem_KL <;> assumption)
