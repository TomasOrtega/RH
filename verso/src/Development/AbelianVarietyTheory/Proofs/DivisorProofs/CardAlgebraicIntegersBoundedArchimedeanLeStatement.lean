import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntCount.card_bounded_integers_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardAlgebraicIntegersBoundedArchimedeanLe.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le : ∀ (E : Type) [Field E] [NumberField E], ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧ ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.IntCount.card_bounded_integers_le | exact GlobalTheory.IntCount.card_bounded_integers_le | (intros; apply GlobalTheory.IntCount.card_bounded_integers_le <;> assumption)
