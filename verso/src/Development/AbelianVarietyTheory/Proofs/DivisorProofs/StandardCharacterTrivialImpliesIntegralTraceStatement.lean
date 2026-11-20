import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTrace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStandardCharacterTrivialImpliesIntegralTrace.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.standard_character_trivial_implies_integral_trace : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) x * t) = 1) → ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  first | exact @GlobalTheory.TraceIntStd.trace_int_of_isStd | exact GlobalTheory.TraceIntStd.trace_int_of_isStd | (intros; apply GlobalTheory.TraceIntStd.trace_int_of_isStd <;> assumption)
