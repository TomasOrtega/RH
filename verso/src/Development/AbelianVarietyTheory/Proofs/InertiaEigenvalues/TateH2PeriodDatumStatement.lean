import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTateH2PeriodDatum.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.tate_H2_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  first | exact @GlobalTheory.TateTop.tateH2_of_duality_loc | exact GlobalTheory.TateTop.tateH2_of_duality_loc | (intros; apply GlobalTheory.TateTop.tateH2_of_duality_loc <;> assumption)
