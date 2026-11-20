import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZero
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousCharacterCocycleTrivialNearZero.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.continuous_character_cocycle_trivial_near_zero : ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  first | exact @GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | exact GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | (intros; apply GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero <;> assumption)
