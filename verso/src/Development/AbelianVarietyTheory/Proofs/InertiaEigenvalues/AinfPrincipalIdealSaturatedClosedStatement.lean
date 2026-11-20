import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AinfSat.mem_ideal_of_saturated` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAinfPrincipalIdealSaturatedClosed.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.ainf_principal_ideal_saturated_closed : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) → ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) → ∃ a : Ainf l, x = inclW l (ι * a) := by
  first | exact @GlobalTheory.AinfSat.mem_ideal_of_saturated | exact GlobalTheory.AinfSat.mem_ideal_of_saturated | (intros; apply GlobalTheory.AinfSat.mem_ideal_of_saturated <;> assumption)
