import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSum
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FScaledIndicatorCosetSum.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.scaled_indicator_coset_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 → ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | exact GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | (intros; apply GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum <;> assumption)
