import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfSchroedingerTranslatesThetaSumZero.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.ThetaInj.main | exact GlobalTheory.ThetaInj.main | (intros; apply GlobalTheory.ThetaInj.main <;> assumption)
