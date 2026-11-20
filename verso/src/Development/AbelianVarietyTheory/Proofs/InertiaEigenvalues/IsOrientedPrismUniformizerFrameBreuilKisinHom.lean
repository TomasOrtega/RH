import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk B f`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f).symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Ideal.span {bk.E}).map (BK.hf f) = _`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Apply `f.f_str` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)`. Simplify using the standard rewrite rules.
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
