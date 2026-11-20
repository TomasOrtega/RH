import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscPeriodBasisIsUnit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKLim.wseed_Z_isUnit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSemistableDiscPeriodBasisIsUnit.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.semistable_disc_period_basis_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  first | exact @GlobalTheory.BKLim.wseed_Z_isUnit | exact GlobalTheory.BKLim.wseed_Z_isUnit | (intros; apply GlobalTheory.BKLim.wseed_Z_isUnit; all_goals assumption)
