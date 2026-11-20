import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwiners
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.intertwiners_indep_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FInjectiveSumOfLinIndepIntertwiners.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.injective_sum_of_linIndep_intertwiners : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  first | exact @GlobalTheory.intertwiners_indep_injective | exact GlobalTheory.intertwiners_indep_injective | (intros; apply GlobalTheory.intertwiners_indep_injective <;> assumption)
