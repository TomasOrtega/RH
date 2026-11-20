import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicSliceSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzAdelicSliceSmooth.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.schwartz_adelic_slice_smooth : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    (∀ y : κ → Af F, ∃ f : SInf F κ, ∀ x, slice Ψ x y = f x) ∧ ∀ x, slice Ψ x ∈ SB (κ → Af F) := by
  first | exact @GlobalTheory.VacLine.slice_schA | exact GlobalTheory.VacLine.slice_schA | (intros; apply GlobalTheory.VacLine.slice_schA <;> assumption)
