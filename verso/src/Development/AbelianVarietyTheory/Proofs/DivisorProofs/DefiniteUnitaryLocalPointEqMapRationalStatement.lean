import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRational
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.LocVal.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDefiniteUnitaryLocalPointEqMapRational.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  first | exact @GlobalTheory.BCT.LocVal.main | exact GlobalTheory.BCT.LocVal.main | (intros; apply GlobalTheory.BCT.LocVal.main <;> assumption)
