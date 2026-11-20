import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.TrKer.continuous_coef_wInf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousMatrixCoeffInfinitePlacesWeightRep.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.continuous_matrixCoeff_infinitePlacesWeightRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := by
  first | exact @GlobalTheory.BCT.TrKer.continuous_coef_wInf | exact GlobalTheory.BCT.TrKer.continuous_coef_wInf | (intros; apply GlobalTheory.BCT.TrKer.continuous_coef_wInf <;> assumption)
