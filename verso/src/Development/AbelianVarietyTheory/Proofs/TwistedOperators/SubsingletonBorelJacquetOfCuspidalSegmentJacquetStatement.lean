import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSubsingletonBorelJacquetOfCuspidalSegmentJacquet.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.subsingleton_borelJacquet_of_cuspidal_segment_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (l d : ℕ), 0 < l → 1 < d → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W) (π : Representation ℂ (GL (Fin (l * d)) k) V), IsCuspidal σ → (∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d), Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) → Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  first | exact @GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | exact GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | (intros; apply GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB <;> assumption)
