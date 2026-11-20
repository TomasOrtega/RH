import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.SingleQ.stepAt_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSingleBlockDoublingIntegralValue.lean&line=368#L368)
-/
theorem _root_.GlobalTheory.T.singleBlock_doublingIntegral_value : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ ν : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → IsNu P ν → ∀ r t : ℕ, 1 ≤ t → StepAt P δ (fun _ => ν) r t 0 (zVal1 (qP P) r t : ℂ) := by
  first | exact @GlobalTheory.Mem.SingleQ.stepAt_one | exact GlobalTheory.Mem.SingleQ.stepAt_one | (intros; apply GlobalTheory.Mem.SingleQ.stepAt_one <;> assumption)
