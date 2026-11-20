import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaGaloisFixedOfCongrBreuilKisin
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKLim.theta_gal_fixed_of_congr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FThetaGaloisFixedOfCongrBreuilKisin.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.theta_galois_fixed_of_congr_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Per.BdRp l) (M k : ℕ) (s : bk.S), (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l (M + 1) → ∀ g : ↥(GK K), Per.σC (g : GQ l) (Per.θD l x) = Per.θD l x := by
  first | exact @GlobalTheory.BKLim.theta_gal_fixed_of_congr | exact GlobalTheory.BKLim.theta_gal_fixed_of_congr | (intros; apply GlobalTheory.BKLim.theta_gal_fixed_of_congr <;> assumption)
