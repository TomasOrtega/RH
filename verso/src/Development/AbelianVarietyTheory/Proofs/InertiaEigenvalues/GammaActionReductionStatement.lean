import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGammaActionReduction.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  first | exact @GlobalTheory.RedAct.gamma_action_reduction | exact GlobalTheory.RedAct.gamma_action_reduction | (intros; apply GlobalTheory.RedAct.gamma_action_reduction <;> assumption)
