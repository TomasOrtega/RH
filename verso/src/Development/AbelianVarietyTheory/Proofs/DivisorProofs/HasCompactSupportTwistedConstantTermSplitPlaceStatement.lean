import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasCompactSupportTwistedConstantTermSplitPlace.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | exact GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | (intros; apply GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split <;> assumption)
