import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanish
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.mem_closure_of_forall_dual_vanish` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMemClosureOfForallDualVanish.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.mem_closure_of_forall_clm_vanish : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  first | exact @GlobalTheory.mem_closure_of_forall_dual_vanish | exact GlobalTheory.mem_closure_of_forall_dual_vanish | (intros; apply GlobalTheory.mem_closure_of_forall_dual_vanish <;> assumption)
