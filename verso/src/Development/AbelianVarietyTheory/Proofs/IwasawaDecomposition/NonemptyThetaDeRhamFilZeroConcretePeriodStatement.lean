import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNonemptyThetaDeRhamFilZeroConcretePeriod.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  first | exact @GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | exact GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | (intros; apply GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL <;> assumption)
