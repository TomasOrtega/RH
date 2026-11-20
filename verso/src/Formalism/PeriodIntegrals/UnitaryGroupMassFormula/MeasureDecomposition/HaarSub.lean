import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ K hK`. Use `haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `hm : haarSub K hK = (Measure.haar : Measure K).map Subtype.val` using `rfl`. Establish `hmeas : Measurable (Subtype.val : K → G)` using `measurable_subtype_coe`. Establish `hcpt : ∀ C : Set G, IsCompact C → haarSub K hK C < ⊤`.

Introduce `C hC`. Rewrite using `[hm, Measure.map_apply hmeas hC.isClosed.measurableSet]`. Conclude with `(hK.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top`. Use `haveI : IsFiniteMeasureOnCompacts (haarSub K hK) := ⟨hcpt⟩`. Use `⟨inferInstance, ?_, ?_, ?_, hcpt, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Rewrite `h0` using `[hm, Measure.map_eq_zero_iff hmeas.aemeasurable]`. Conclude with `isOpen_univ.measure_ne_zero (Measure.haar : Measure K) Set.univ_nonempty (by simp [h0])`. Rewrite using `[hm, Measure.map_apply hmeas hK.isOpen_compl.measurableSet]`. Establish `hpre : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_not]`. Conclude with `x.2`. Rewrite using `[hpre, measure_empty]`. Introduce `s hs`.

Rewrite using `[hm, Measure.map_map (measurable_const_mul s) hmeas]`. Establish `hcomp : (fun x => s * x) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun y : K => (⟨s, hs⟩ : K) * y)`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression. Rewrite using `[hcomp, ← Measure.map_map hmeas (measurable_const_mul _)]`.

Use `congr 1`. Use `first`. Consider the case `exact map_mul_left_eq_self (Measure.haar : Measure K) _`. Consider the case `exact Measure.IsMulLeftInvariant.map_mul_left_eq_self _`. Introduce `U hU h1`.

Rewrite using `[hm, Measure.map_apply hmeas hU.measurableSet]`. Conclude with `(hU.preimage continuous_subtype_val).measure_pos (Measure.haar : Measure K) ⟨1, by simpa using h1⟩`.
-/
theorem generic_haar_subgroup : GenHaarSub := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hm : haarSub K hK = (Measure.haar : Measure K).map Subtype.val := rfl
  have hmeas : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hcpt : ∀ C : Set G, IsCompact C → haarSub K hK C < ⊤ := by
    intro C hC
    rw [hm, Measure.map_apply hmeas hC.isClosed.measurableSet]
    exact (hK.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top
  haveI : IsFiniteMeasureOnCompacts (haarSub K hK) := ⟨hcpt⟩
  refine ⟨inferInstance, ?_, ?_, ?_, hcpt, ?_⟩
  · intro h0
    rw [hm, Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (Measure.haar : Measure K) Set.univ_nonempty (by simp [h0])
  · rw [hm, Measure.map_apply hmeas hK.isOpen_compl.measurableSet]
    have hpre : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact x.2
    rw [hpre, measure_empty]
  · intro s hs
    rw [hm, Measure.map_map (measurable_const_mul s) hmeas]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : K → G) =
        Subtype.val ∘ (fun y : K => (⟨s, hs⟩ : K) * y) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _)]
    congr 1
    first
      | exact map_mul_left_eq_self (Measure.haar : Measure K) _
      | exact Measure.IsMulLeftInvariant.map_mul_left_eq_self _
  · intro U hU h1
    rw [hm, Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_pos (Measure.haar : Measure K) ⟨1, by simpa using h1⟩

end PI.ScMuExists.UnitaryGroupMassFormula
