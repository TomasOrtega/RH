import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GeoFix.exists_inR_mul_eq_psi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCombinationMulEqReparametrizationImage.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_combination_mul_eq_reparametrization_image : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 → ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  first | exact @GlobalTheory.GeoFix.exists_inR_mul_eq_psi | exact GlobalTheory.GeoFix.exists_inR_mul_eq_psi | (intros; apply GlobalTheory.GeoFix.exists_inR_mul_eq_psi <;> assumption)
