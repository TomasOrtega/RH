import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Per.FontaineTied.fontCore_all_of_tied` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFontaineBoundsCrystallineDeRhamConcreteRings.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.fontaine_bounds_crystalline_deRham_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  first | exact @GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | exact GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | (intros; apply GlobalTheory.Per.FontaineTied.fontCore_all_of_tied <;> assumption)
