import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMultisetSatakeEigenvalueEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsMultisetSatakeEigenvalueEq.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_multiset_satakeEigenvalue_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 → ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  first | exact @GlobalTheory.LFun.exists_satEig_eq | exact GlobalTheory.LFun.exists_satEig_eq | (intros; apply GlobalTheory.LFun.exists_satEig_eq <;> assumption)
