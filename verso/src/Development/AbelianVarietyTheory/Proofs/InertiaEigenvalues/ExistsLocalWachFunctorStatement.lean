import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctor
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HWL.Assembly.exists_wach` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLocalWachFunctor.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_local_wach_functor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → FaithH AI → WachEx AI → ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  first | exact @GlobalTheory.HWL.Assembly.exists_wach | exact GlobalTheory.HWL.Assembly.exists_wach | (intros; apply GlobalTheory.HWL.Assembly.exists_wach <;> assumption)
