import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLineAdmissibleCocyclesNotIndependent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TopSteps.TrivLine.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTrivialLineAdmissibleCocyclesNotIndependent.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.trivialLine_admissibleCocycles_not_independent : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ z : Fin 2 → G → Fin 1 → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles (chr 1)) → ¬ LinearIndependent k (fun a => (cob (chr (1 : G →* kˣ))).mkQ (z a)) := by
  first | exact @GlobalTheory.TopSteps.TrivLine.main | exact GlobalTheory.TopSteps.TrivLine.main | (intros; apply GlobalTheory.TopSteps.TrivLine.main <;> assumption)
