import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrix
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsCrystallineOfInvariantUnitBcrisMatrix.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isCrystalline_of_invariant_unit_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  first | exact @GlobalTheory.BKLim.isCrys_of_bcris_matrix | exact GlobalTheory.BKLim.isCrys_of_bcris_matrix | (intros; apply GlobalTheory.BKLim.isCrys_of_bcris_matrix <;> assumption)
