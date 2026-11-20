import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfect
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WittTeichComplete.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittVectorTeichmullerIsAdicCompleteOfPerfect.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O → IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔ Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  first | exact @GlobalTheory.WittTeichComplete.main | exact GlobalTheory.WittTeichComplete.main | (intros; apply GlobalTheory.WittTeichComplete.main <;> assumption)
