import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

noncomputable section

open MeasureTheory Topology

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} {ε : Fin n → Bool}

def haarSub (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) : Measure (Formalism.REAL.UJ ε) :=
  haveI : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  (Measure.haar : Measure G).map Subtype.val

/- English proof (translation)
Establish `: LocallyCompactSpace G` using `hG.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `hemb` using `hG.isClosedEmbedding_subtypeVal`. Establish `hι : Measurable (Subtype.val : G → Formalism.REAL.UJ ε)` using `measurable_subtype_coe`. Establish `hfin : IsFiniteMeasureOnCompacts (haarSub G hG)`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations.

Rewrite using `[haarSub, Measure.map_apply hι hK.measurableSet]`. Conclude with `(hemb.isCompact_preimage hK).measure_lt_top`. Use `⟨⟨?_, ?_, ?_, ?_⟩, hfin⟩` and prove the remaining obligations. Use `hfin infer_instance` as an intermediate fact. Rewrite using `[haarSub, Ne, Measure.map_eq_zero_iff hι.aemeasurable]`.

Conclude with `NeZero.ne _`. Rewrite using `[haarSub, Measure.map_apply hι hG.measurableSet.compl]`. Establish `hempty : (Subtype.val : G → Formalism.REAL.UJ ε) ⁻¹' (G : Set (Formalism.REAL.UJ ε))ᶜ = ∅`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[hempty, measure_empty]`. Introduce `s hs`. Rewrite using `[haarSub, Measure.map_map (measurable_const_mul s) hι]`. Establish `hcomp : (fun x => s * x) ∘ (Subtype.val : G → Formalism.REAL.UJ ε) = Subtype.val ∘ (fun y : G => (⟨s, hs⟩ : G) * y)` using `rfl`. Rewrite using `[hcomp, ← Measure.map_map hι (measurable_const_mul _), map_mul_left_eq_self]`.
-/
theorem haarSub_isHaarS (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) :
    IsHaarS (G : Set (Formalism.REAL.UJ ε)) (haarSub G hG) := by
  have : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb := hG.isClosedEmbedding_subtypeVal
  have hι : Measurable (Subtype.val : G → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have hfin : IsFiniteMeasureOnCompacts (haarSub G hG) := by
    refine ⟨fun K hK => ?_⟩
    rw [haarSub, Measure.map_apply hι hK.measurableSet]
    exact (hemb.isCompact_preimage hK).measure_lt_top
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin⟩
  · have := hfin
    infer_instance
  · rw [haarSub, Ne, Measure.map_eq_zero_iff hι.aemeasurable]
    exact NeZero.ne _
  · rw [haarSub, Measure.map_apply hι hG.measurableSet.compl]
    have hempty : (Subtype.val : G → Formalism.REAL.UJ ε) ⁻¹' (G : Set (Formalism.REAL.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [hempty, measure_empty]
  · intro s hs
    rw [haarSub, Measure.map_map (measurable_const_mul s) hι]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : G → Formalism.REAL.UJ ε) =
        Subtype.val ∘ (fun y : G => (⟨s, hs⟩ : G) * y) := rfl
    rw [hcomp, ← Measure.map_map hι (measurable_const_mul _), map_mul_left_eq_self]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
