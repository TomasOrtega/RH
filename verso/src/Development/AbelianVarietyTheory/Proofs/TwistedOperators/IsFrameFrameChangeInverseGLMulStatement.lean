import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameFrameChangeInverseGLMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsFrameFrameChangeInverseGLMul.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.isFrame_frameChangeInverseGL_mul : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := by
  first | exact @GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul | exact GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul | (intros; apply GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul <;> assumption)
