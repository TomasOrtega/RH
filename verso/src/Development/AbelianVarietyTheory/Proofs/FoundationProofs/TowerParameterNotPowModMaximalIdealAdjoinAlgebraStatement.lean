import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterNotPowModMaximalIdealAdjoinAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.NotPow.not_pow_mod_max` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTowerParameterNotPowModMaximalIdealAdjoinAlgebra.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  first | exact @GlobalTheory.K5.NotPow.not_pow_mod_max | exact GlobalTheory.K5.NotPow.not_pow_mod_max | (intros; apply GlobalTheory.K5.NotPow.not_pow_mod_max <;> assumption)
