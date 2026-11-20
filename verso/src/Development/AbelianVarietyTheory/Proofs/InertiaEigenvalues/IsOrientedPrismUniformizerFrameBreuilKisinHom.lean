import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem isFrame_hf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f : Hom bk.prism B), IsFrame bk B (BK.hf f bk.E) (BK.hf f X) := by
  intro l _ K bk B f
  refine ⟨?_, ?_⟩
  · refine (GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f).symm.trans ?_
    change (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  · apply f.f_str
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)
    simp

end GlobalTheory.BSP
