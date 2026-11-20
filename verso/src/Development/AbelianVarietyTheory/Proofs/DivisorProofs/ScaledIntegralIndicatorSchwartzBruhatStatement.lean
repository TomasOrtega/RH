import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIntegralIndicatorSchwartzBruhat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FScaledIntegralIndicatorSchwartzBruhat.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.scaled_integral_indicator_schwartz_bruhat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.EvAdm.indicator_sub_mem_scaledInt_mem_SB | exact GlobalTheory.EvAdm.indicator_sub_mem_scaledInt_mem_SB | (intros; apply GlobalTheory.EvAdm.indicator_sub_mem_scaledInt_mem_SB <;> assumption)
