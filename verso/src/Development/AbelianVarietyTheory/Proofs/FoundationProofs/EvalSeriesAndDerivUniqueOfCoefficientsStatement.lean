import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEvalSeriesAndDerivUniqueOfCoefficients.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω), Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  first | exact @GlobalTheory.EvUniq.ev_unique | exact GlobalTheory.EvUniq.ev_unique | (intros; apply GlobalTheory.EvUniq.ev_unique <;> assumption)
