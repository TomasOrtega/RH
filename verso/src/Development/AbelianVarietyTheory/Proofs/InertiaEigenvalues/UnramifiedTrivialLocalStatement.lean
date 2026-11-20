import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocal
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnramifiedTrivial.unrTriv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedTrivialLocal.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.unramified_trivial_local : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  first | exact @GlobalTheory.UnramifiedTrivial.unrTriv | exact GlobalTheory.UnramifiedTrivial.unrTriv | (intros; apply GlobalTheory.UnramifiedTrivial.unrTriv <;> assumption)
