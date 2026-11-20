import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.CtReg.ctMu_regAt2` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwistedConstantTermSplitPlaceRegular.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.twistedConstantTermSplitPlace_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtReg.ctMu_regAt2 | exact GlobalTheory.BCT.CtReg.ctMu_regAt2 | (intros; apply GlobalTheory.BCT.CtReg.ctMu_regAt2 <;> assumption)
