import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTwoBlockEquiv
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCellFunctorTwoBlockEquiv.lean&line=240#L240)
-/
theorem _root_.GlobalTheory.T.cell_functor_two_block_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))), b.1 false true = 0 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j),
      Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
          (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
            (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom)
        (extTensor (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2)))))
          (detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2))))) := by
  first | exact @GlobalTheory.CellDetFirst.main | exact GlobalTheory.CellDetFirst.main | (intros; apply GlobalTheory.CellDetFirst.main <;> assumption)
