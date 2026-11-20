import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TiltFaithful.faithH` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicKernelTiltInvariantsFaithful.lean&line=260#L260)
-/
theorem _root_.GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  first | exact @GlobalTheory.TiltFaithful.faithH | exact GlobalTheory.TiltFaithful.faithH | (intros; apply GlobalTheory.TiltFaithful.faithH <;> assumption)
