import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAutomorphicFormGLTameOfFinitenessAtRank.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  first | exact @GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank | exact GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank | (intros; apply GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank <;> assumption)
