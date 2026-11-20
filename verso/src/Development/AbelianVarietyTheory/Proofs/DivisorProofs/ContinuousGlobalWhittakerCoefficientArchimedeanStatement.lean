import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedean
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousGlobalWhittakerCoefficientArchimedean.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ g h : GA E a, Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  first | exact @GlobalTheory.JSW.continuous_whit_infGL | exact GlobalTheory.JSW.continuous_whit_infGL | (intros; apply GlobalTheory.JSW.continuous_whit_infGL <;> assumption)
