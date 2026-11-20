import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqOfIntegralsEq
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzEqOfIntegralsEq.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.schwartz_eq_of_integrals_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ f ∈ schA F κ, ∀ g ∈ schA F κ,
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ ψ ∈ schA F κ,
      ∫ x, f x * starRingEnd ℂ (ψ x) ∂μ = ∫ x, g x * starRingEnd ℂ (ψ x) ∂μ) → f = g := by
  first | exact @GlobalTheory.SchAPairing.eq_of_pairing | exact GlobalTheory.SchAPairing.eq_of_pairing | (intros; apply GlobalTheory.SchAPairing.eq_of_pairing <;> assumption)
