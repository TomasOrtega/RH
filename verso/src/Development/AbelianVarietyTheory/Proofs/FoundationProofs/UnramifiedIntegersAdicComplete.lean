import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

/- English proof (translation)
Introduce `p _`. Establish `hfg : (pI p).FG` using `⟨{(p : Lau p)}, by simp⟩`. Establish `h : IsAdicComplete (pI p) (O0 p)` using `AdicCompletion.isAdicComplete hfg`. Establish `hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`.

Rewrite using `[← hmap]`. Conclude with `{ toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 h.toIsHausdorff toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 h.toIsPrecomplete }`.
-/
theorem o0_isAdicComplete_span_p : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  intro p _
  have hfg : (pI p).FG := ⟨{(p : Lau p)}, by simp⟩
  have h : IsAdicComplete (pI p) (O0 p) := AdicCompletion.isAdicComplete hfg
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 h.toIsHausdorff
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 h.toIsPrecomplete }

end GlobalTheory.K5
