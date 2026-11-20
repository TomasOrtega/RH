import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalAtCompletionIntegersChosenUniformiser
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsLocalAtCompletionIntegersChosenUniformiser.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  first | exact @GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer | exact GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer | (intros; apply GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer <;> assumption)
