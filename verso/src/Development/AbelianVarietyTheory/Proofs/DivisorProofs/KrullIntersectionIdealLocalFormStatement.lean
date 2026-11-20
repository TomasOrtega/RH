import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalForm
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.krull_inter_ideal_local` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKrullIntersectionIdealLocalForm.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  first | exact @GlobalTheory.krull_inter_ideal_local | exact GlobalTheory.krull_inter_ideal_local | (intros; apply GlobalTheory.krull_inter_ideal_local <;> assumption)
