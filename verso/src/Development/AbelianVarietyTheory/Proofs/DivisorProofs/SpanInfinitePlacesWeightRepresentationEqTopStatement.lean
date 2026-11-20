import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpanInfinitePlacesWeightRepresentationEqTop.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | exact GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | (intros; apply GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top <;> assumption)
