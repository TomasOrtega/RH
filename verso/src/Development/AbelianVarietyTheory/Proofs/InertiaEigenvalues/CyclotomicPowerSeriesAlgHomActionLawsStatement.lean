import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicPowerSeriesAlgHomActionLaws.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  first | exact @GlobalTheory.Cyc.act_laws | exact GlobalTheory.Cyc.act_laws | (intros; apply GlobalTheory.Cyc.act_laws <;> assumption)
