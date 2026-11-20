import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardResidueRingCompletionChosenUniformiser
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCardResidueRingCompletionChosenUniformiser.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.card_residueRing_completion_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  first | exact @GlobalTheory.ResidueCardUnif.card_kF_piP | exact GlobalTheory.ResidueCardUnif.card_kF_piP | (intros; apply GlobalTheory.ResidueCardUnif.card_kF_piP <;> assumption)
