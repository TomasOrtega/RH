import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobCong.sigma_eq_pow_add` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittTiltFrobeniusEqPowAddMul.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  first | exact @GlobalTheory.FrobCong.sigma_eq_pow_add | exact GlobalTheory.FrobCong.sigma_eq_pow_add | (intros; apply GlobalTheory.FrobCong.sigma_eq_pow_add <;> assumption)
