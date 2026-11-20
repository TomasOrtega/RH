import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cyc.exists_isTheta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsFontaineThetaOnAinf.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_fontaineTheta_on_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ∃ θ : Ainf l →+* OC l, IsTheta AI θ := by
  first | exact @GlobalTheory.Cyc.exists_isTheta | exact GlobalTheory.Cyc.exists_isTheta | (intros; apply GlobalTheory.Cyc.exists_isTheta <;> assumption)
