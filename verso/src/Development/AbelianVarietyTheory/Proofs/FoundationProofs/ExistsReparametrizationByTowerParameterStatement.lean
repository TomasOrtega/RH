import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Glue.exists_isReb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsReparametrizationByTowerParameter.lean&line=285#L285)
-/
theorem _root_.GlobalTheory.T.exists_reparametrizationByTowerParameter : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∃ ψ : O0 p →+* Ω, IsReb T n ψ := by
  first | exact @GlobalTheory.Glue.exists_isReb | exact GlobalTheory.Glue.exists_isReb | (intros; apply GlobalTheory.Glue.exists_isReb <;> assumption)
