import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpanTranslatesOfNonzeroSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalSpanTranslatesOfNonzeroSchwartz.lean&line=263#L263)
-/
theorem _root_.GlobalTheory.T.local_span_translates_of_nonzero_schwartz : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F), Continuous (psiLoc ψ v) →
    (∃ x : Fv F v, psiLoc ψ v x ≠ 1) → ∀ {κ : Type} [Fintype κ] (φ₀ φ : (κ → Fv F v) → ℂ), φ₀ ∈ SB _ → φ₀ ≠ 0 →
    φ ∈ SB _ → φ ∈ Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) := by
  first | exact @GlobalTheory.SchrCyclic.mem_span_locOp | exact GlobalTheory.SchrCyclic.mem_span_locOp | (intros; apply GlobalTheory.SchrCyclic.mem_span_locOp <;> assumption)
