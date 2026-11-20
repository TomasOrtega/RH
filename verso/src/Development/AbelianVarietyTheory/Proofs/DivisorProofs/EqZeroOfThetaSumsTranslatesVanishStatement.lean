import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfThetaSumsTranslatesVanish
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfThetaSumsTranslatesVanish.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_theta_sums_translates_vanish : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (h : (κ → AF F) → ℂ), h ∈ schA F κ → (∀ x y : κ → AF F, thetaSum F (schr ψ (x, y) h) = 0) → h = 0 := by
  first | exact @GlobalTheory.ThetaSep.main | exact GlobalTheory.ThetaSep.main | (intros; apply GlobalTheory.ThetaSep.main <;> assumption)
