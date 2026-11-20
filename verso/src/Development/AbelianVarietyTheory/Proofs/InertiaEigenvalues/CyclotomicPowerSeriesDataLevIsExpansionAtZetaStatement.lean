import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZeta
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HWL.LevExp.lev_isExp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicPowerSeriesDataLevIsExpansionAtZeta.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  first | exact @GlobalTheory.HWL.LevExp.lev_isExp | exact GlobalTheory.HWL.LevExp.lev_isExp | (intros; apply GlobalTheory.HWL.LevExp.lev_isExp <;> assumption)
