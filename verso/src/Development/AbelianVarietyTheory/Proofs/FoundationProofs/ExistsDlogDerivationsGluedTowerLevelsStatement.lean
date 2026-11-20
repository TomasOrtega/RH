import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevels
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevGlue.glue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsDlogDerivationsGluedTowerLevels.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.exists_dlog_derivations_glued_tower_levels : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
  (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
  ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  first | exact @GlobalTheory.LevGlue.glue | exact GlobalTheory.LevGlue.glue | (intros; apply GlobalTheory.LevGlue.glue <;> assumption)
