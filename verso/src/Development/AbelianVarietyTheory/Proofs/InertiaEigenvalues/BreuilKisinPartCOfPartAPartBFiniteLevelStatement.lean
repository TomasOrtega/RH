import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevel
import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKFinLevel.bkC_of_bkA_bkB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinPartCOfPartAPartBFiniteLevel.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  first | exact @GlobalTheory.BKFinLevel.bkC_of_bkA_bkB | exact GlobalTheory.BKFinLevel.bkC_of_bkA_bkB | (intros; apply GlobalTheory.BKFinLevel.bkC_of_bkA_bkB <;> assumption)
