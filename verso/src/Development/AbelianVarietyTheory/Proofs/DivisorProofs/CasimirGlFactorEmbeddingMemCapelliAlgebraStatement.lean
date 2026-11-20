import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCasimirGlFactorEmbeddingMemCapelliAlgebra.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CasCentre.cas_Eop_mem_Zalg | exact GlobalTheory.CasCentre.cas_Eop_mem_Zalg | (intros; apply GlobalTheory.CasCentre.cas_Eop_mem_Zalg <;> assumption)
