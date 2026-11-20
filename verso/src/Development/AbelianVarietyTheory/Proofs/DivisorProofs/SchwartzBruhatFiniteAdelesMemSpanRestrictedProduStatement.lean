import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SBSpan.mem_span_restrictedProd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzBruhatFiniteAdelesMemSpanRestrictedProdu.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ SB (κ → Af F),
    g ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)} := by
  first | exact @GlobalTheory.SBSpan.mem_span_restrictedProd | exact GlobalTheory.SBSpan.mem_span_restrictedProd | (intros; apply GlobalTheory.SBSpan.mem_span_restrictedProd <;> assumption)
