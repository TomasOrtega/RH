import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceDualLatticeBoundedDenominator.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.trace_dual_lattice_bounded_denominator : ∀ {F : Type} [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ ξ : F, (∀ o : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * o) = z) → ∃ o : 𝓞 F, (D : F) * ξ = o := by
  first | exact @GlobalTheory.exists_den_traceDual_ringOfIntegers | exact GlobalTheory.exists_den_traceDual_ringOfIntegers | (intros; apply GlobalTheory.exists_den_traceDual_ringOfIntegers <;> assumption)
