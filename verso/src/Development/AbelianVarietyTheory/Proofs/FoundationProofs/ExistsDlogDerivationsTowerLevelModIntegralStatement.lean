import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsTowerLevelModIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevDer.exists_levDer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsDlogDerivationsTowerLevelModIntegral.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
  ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  first | exact @GlobalTheory.LevDer.exists_levDer | exact GlobalTheory.LevDer.exists_levDer | (intros; apply GlobalTheory.LevDer.exists_levDer <;> assumption)
