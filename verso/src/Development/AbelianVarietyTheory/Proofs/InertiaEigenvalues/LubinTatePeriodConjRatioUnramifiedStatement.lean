import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.lt_period_conj_ratio` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLubinTatePeriodConjRatioUnramified.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.lubinTate_period_conj_ratio_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  first | exact @GlobalTheory.PMon.lt_period_conj_ratio | exact GlobalTheory.PMon.lt_period_conj_ratio | (intros; apply GlobalTheory.PMon.lt_period_conj_ratio <;> assumption)
