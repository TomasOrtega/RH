import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringPullbackIntegralElements
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsValuationSubringPullbackIntegralElements.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_valuationSubring_pullback_integral_elements : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧ ∀ x, x ∈ B ↔ IsInt p (j x) := by
  first | exact @GlobalTheory.K5.exists_valuationSubring_isInt_comap | exact GlobalTheory.K5.exists_valuationSubring_isInt_comap | (intros; apply GlobalTheory.K5.exists_valuationSubring_isInt_comap <;> assumption)
