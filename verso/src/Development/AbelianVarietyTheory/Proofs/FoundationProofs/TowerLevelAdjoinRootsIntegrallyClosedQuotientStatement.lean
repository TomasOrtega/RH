import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotient
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.LevClosed.lev_closed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTowerLevelAdjoinRootsIntegrallyClosedQuotient.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
  IsInt p (a / b) → a / b ∈ Lev T m := by
  first | exact @GlobalTheory.K5.LevClosed.lev_closed | exact GlobalTheory.K5.LevClosed.lev_closed | (intros; apply GlobalTheory.K5.LevClosed.lev_closed <;> assumption)
