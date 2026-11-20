import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisFixedEqDivLevelElements
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTowerGaloisFixedEqDivLevelElements.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.towerGaloisFixed_eq_div_levelElements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
  ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  first | exact @GlobalTheory.FixFrac.fixed_eq_div | exact GlobalTheory.FixFrac.fixed_eq_div | (intros; apply GlobalTheory.FixFrac.fixed_eq_div <;> assumption)
