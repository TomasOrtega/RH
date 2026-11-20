import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionFactorizesAlmostAll
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchAFactor.exists_tens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzFunctionFactorizesAlmostAll.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.schwartz_function_factorizes_almost_all : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T →
    ∃ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), Rest (evFin F v) φ r ∧ Φ = tens (evFin F v) φ r := by
  first | exact @GlobalTheory.SchAFactor.exists_tens | exact GlobalTheory.SchAFactor.exists_tens | (intros; apply GlobalTheory.SchAFactor.exists_tens <;> assumption)
