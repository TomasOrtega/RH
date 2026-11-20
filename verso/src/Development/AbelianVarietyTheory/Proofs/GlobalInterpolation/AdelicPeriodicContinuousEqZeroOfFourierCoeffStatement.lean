import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FAdelicPeriodicContinuousEqZeroOfFourierCoeff.lean&line=366#L366)
-/
theorem _root_.GlobalTheory.T.adelicPeriodic_continuous_eq_zero_of_fourier_coeff : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ P : (Fin N → AF F) → ℂ, Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ : Fin N → F, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0) → P = 0 := by
  first | exact @GlobalTheory.SWQ.periodic_eq_zero_of_coeff | exact GlobalTheory.SWQ.periodic_eq_zero_of_coeff | (intros; apply GlobalTheory.SWQ.periodic_eq_zero_of_coeff <;> assumption)
