import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRoundedTwistLocalEquationChart.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.roundedTwist_localEquation_chart : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  first | exact @GlobalTheory.roundedTwist_isEqn | exact GlobalTheory.roundedTwist_isEqn | (intros; apply GlobalTheory.roundedTwist_isEqn <;> assumption)
