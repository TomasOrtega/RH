import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarishChandraFiniteFormsGLSingleCharSpanMem.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.harishChandraFiniteFormsGL_single_char_span_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  first | exact @GlobalTheory.HCF.formsGL_single_span | exact GlobalTheory.HCF.formsGL_single_span | (intros; apply GlobalTheory.HCF.formsGL_single_span <;> assumption)
