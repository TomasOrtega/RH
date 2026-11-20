import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
Unfold `GenSemi`. Introduce `G _ _ _ _ _ _ _ _ N H hN hH hconj hinvN hprop`. Take `⟨hσN, -, hcN, htN, hfinN, hposN⟩` from `hHaar G N hN`. Take `⟨hσH, -, hcH, htH, hfinH, hposH⟩` from `hHaar G H hH`. Use `set μN := haarSub N hN with hμN`.

Use `set μH := haarSub H hH with hμH`. Use `haveI : SigmaFinite μN := hσN`. Use `haveI : SigmaFinite μH := hσH`. Establish `hmul : Measurable (fun p : G × G => p.1 * p.2)` using `measurable_fst.mul measurable_snd`. Establish `hNH : (N : Set G) * (H : Set G) = (fun p : G × G => p.1 * p.2) '' ((N : Set G) ×ˢ (H : Set G))`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨(a, b), ⟨ha, hb⟩, rfl⟩`. Introduce and unpack `⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩`.

Conclude with `⟨a, ha, b, hb, rfl⟩`. Establish `hmeasNH : MeasurableSet ((N : Set G) * (H : Set G))`. Rewrite using `[hNH]`. Take `⟨K, hK, hKU⟩` from `(isSigmaCompact_univ.of_isClosed_subset (hN.prod hH) (Set.subset_univ _)).image continuous_mul`. Rewrite using `[← hKU]`.

Conclude with `MeasurableSet.iUnion fun n => (hK n).measurableSet`. Establish `hprodc : (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ = 0`. Rewrite using `[Set.compl_prod_eq_union]`. Use `measure_union_null ?_ ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_prod, hcN, zero_mul]`.

Rewrite using `[Measure.prod_prod, hcH, mul_zero]`. Use `⟨?_, hmeasNH, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show SFinite ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) infer_instance`. Use `show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) ((N : Set G) * (H : Set G))ᶜ = 0`. Rewrite using `[Measure.map_apply hmul hmeasNH.compl]`.

Use `measure_mono_null ?_ hprodc` and prove the remaining obligations. Introduce `p hp hpNH`. Conclude with `hp ⟨p.1, hpNH.1, p.2, hpNH.2, rfl⟩`. Introduce and unpack `t ⟨n0, hn0, h0, hh0, rfl⟩ show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)).map (fun x => n0 * h0 * x) = (μN.prod μH).map (fun p : G × G => p.1 * p.2)`. Establish `hc : Measurable (fun x : G => h0 * x * h0⁻¹)` using `(measurable_const_mul h0).mul_const _`.

Establish `hf : Measurable (fun x : G => n0 * (h0 * x * h0⁻¹))` using `(measurable_const_mul n0).comp hc`. Establish `hg : Measurable (fun y : G => h0 * y)` using `measurable_const_mul h0`. Establish `hfN : μN.map (fun x : G => n0 * (h0 * x * h0⁻¹)) = μN` using `by show μN.map ((fun x : G => n0 * x) ∘ (fun x : G => h0 * x * h0⁻¹)) = μN`. Rewrite using `[← Measure.map_map (measurable_const_mul n0) hc, hinvN h0 hh0, htN n0 hn0]`. Establish `hgH : μH.map (fun y : G => h0 * y) = μH` using `htH h0 hh0`.

Establish `hPM : Measurable (Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y))` using `hf.prodMap hg`. Establish `hcomp : (fun x : G => n0 * h0 * x) ∘ (fun p : G × G => p.1 * p.2) = (fun p : G × G => p.1 * p.2) ∘ Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y)`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, Prod.map_fst, Prod.map_snd]`. Use `group`.

Rewrite using `[Measure.map_map (measurable_const_mul _) hmul, hcomp, ← Measure.map_map hmul hPM, ← Measure.map_prod_map μN μH hf hg, hfN, hgH]`. Introduce `U hU h1U show 0 < ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) U`. Rewrite using `[Measure.map_apply hmul hU.measurableSet]`. Establish `hUo : IsOpen ((fun p : G × G => p.1 * p.2) ⁻¹' U)` using `hU.preimage continuous_mul`. Establish `h11 : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1 * p.2) ⁻¹' U` using `by show (1 : G) * 1 ∈ U`.

Rewrite using `[one_mul]` and apply the resulting hypothesis. Take `⟨u, v, hu, hv, h1u, h1v, huv⟩` from `isOpen_prod_iff.mp hUo 1 1 h11`. Combine the equalities or inequalities in the displayed calculation. Introduce `C hC show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) C < ⊤`. Rewrite using `[Measure.map_apply hmul hC.measurableSet]`.

Establish `hK` using `hprop C hC`. Use `set P := {p : G × G | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} with hP`. Establish `hsub : (fun p : G × G => p.1 * p.2) ⁻¹' C ⊆ P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ`. Introduce `p hp`. Distinguish the cases in `h : p ∈ (N : Set G) ×ˢ (H : Set G)`.

Conclude with `Or.inl ⟨h.1, h.2, hp⟩`. Conclude with `Or.inr h`. Establish `hPbox : P ⊆ (Prod.fst '' P) ×ˢ (Prod.snd '' P)` using `fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩`. Establish `hPfin : (μN.prod μH) P < ⊤`. Use `lt_of_le_of_lt (measure_mono hPbox) ?_` and prove the remaining obligations.

Rewrite using `[Measure.prod_prod]`. Conclude with `ENNReal.mul_lt_top (hfinN _ (hK.image continuous_fst)) (hfinH _ (hK.image continuous_snd))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem genSemi_of (hHaar : GenHaarSub) : GenSemi := by
  unfold GenSemi
  intro G _ _ _ _ _ _ _ _ N H hN hH hconj hinvN hprop
  obtain ⟨hσN, -, hcN, htN, hfinN, hposN⟩ := hHaar G N hN
  obtain ⟨hσH, -, hcH, htH, hfinH, hposH⟩ := hHaar G H hH
  set μN := haarSub N hN with hμN
  set μH := haarSub H hH with hμH
  haveI : SigmaFinite μN := hσN
  haveI : SigmaFinite μH := hσH
  have hmul : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd

  have hNH : (N : Set G) * (H : Set G) =
      (fun p : G × G => p.1 * p.2) '' ((N : Set G) ×ˢ (H : Set G)) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hmeasNH : MeasurableSet ((N : Set G) * (H : Set G)) := by
    rw [hNH]
    obtain ⟨K, hK, hKU⟩ := (isSigmaCompact_univ.of_isClosed_subset (hN.prod hH)
      (Set.subset_univ _)).image continuous_mul
    rw [← hKU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet

  have hprodc : (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ = 0 := by
    rw [Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hcN, zero_mul]
    · rw [Measure.prod_prod, hcH, mul_zero]
  refine ⟨?_, hmeasNH, ?_, ?_, ?_, ?_⟩
  · show SFinite ((μN.prod μH).map (fun p : G × G => p.1 * p.2))
    infer_instance
  · show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) ((N : Set G) * (H : Set G))ᶜ = 0
    rw [Measure.map_apply hmul hmeasNH.compl]
    refine measure_mono_null ?_ hprodc
    intro p hp hpNH
    exact hp ⟨p.1, hpNH.1, p.2, hpNH.2, rfl⟩
  · rintro t ⟨n0, hn0, h0, hh0, rfl⟩
    show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)).map (fun x => n0 * h0 * x) =
      (μN.prod μH).map (fun p : G × G => p.1 * p.2)
    have hc : Measurable (fun x : G => h0 * x * h0⁻¹) := (measurable_const_mul h0).mul_const _
    have hf : Measurable (fun x : G => n0 * (h0 * x * h0⁻¹)) := (measurable_const_mul n0).comp hc
    have hg : Measurable (fun y : G => h0 * y) := measurable_const_mul h0
    have hfN : μN.map (fun x : G => n0 * (h0 * x * h0⁻¹)) = μN := by
      show μN.map ((fun x : G => n0 * x) ∘ (fun x : G => h0 * x * h0⁻¹)) = μN
      rw [← Measure.map_map (measurable_const_mul n0) hc, hinvN h0 hh0, htN n0 hn0]
    have hgH : μH.map (fun y : G => h0 * y) = μH := htH h0 hh0
    have hPM : Measurable (Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y)) :=
      hf.prodMap hg
    have hcomp : (fun x : G => n0 * h0 * x) ∘ (fun p : G × G => p.1 * p.2) =
        (fun p : G × G => p.1 * p.2) ∘
          Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y) := by
      funext p
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
      group
    rw [Measure.map_map (measurable_const_mul _) hmul, hcomp, ← Measure.map_map hmul hPM,
      ← Measure.map_prod_map μN μH hf hg, hfN, hgH]
  · intro U hU h1U
    show 0 < ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) U
    rw [Measure.map_apply hmul hU.measurableSet]
    have hUo : IsOpen ((fun p : G × G => p.1 * p.2) ⁻¹' U) := hU.preimage continuous_mul
    have h11 : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1 * p.2) ⁻¹' U := by
      show (1 : G) * 1 ∈ U
      rwa [one_mul]
    obtain ⟨u, v, hu, hv, h1u, h1v, huv⟩ := isOpen_prod_iff.mp hUo 1 1 h11
    calc (0 : ℝ≥0∞) < μN u * μH v := ENNReal.mul_pos (hposN u hu h1u).ne' (hposH v hv h1v).ne'
      _ = (μN.prod μH) (u ×ˢ v) := (Measure.prod_prod u v).symm
      _ ≤ _ := measure_mono huv
  · intro C hC
    show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) C < ⊤
    rw [Measure.map_apply hmul hC.measurableSet]
    have hK := hprop C hC
    set P := {p : G × G | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} with hP
    have hsub : (fun p : G × G => p.1 * p.2) ⁻¹' C ⊆ P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ := by
      intro p hp
      by_cases h : p ∈ (N : Set G) ×ˢ (H : Set G)
      · exact Or.inl ⟨h.1, h.2, hp⟩
      · exact Or.inr h
    have hPbox : P ⊆ (Prod.fst '' P) ×ˢ (Prod.snd '' P) := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
    have hPfin : (μN.prod μH) P < ⊤ := by
      refine lt_of_le_of_lt (measure_mono hPbox) ?_
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top (hfinN _ (hK.image continuous_fst)) (hfinH _ (hK.image continuous_snd))
    calc (μN.prod μH) ((fun p : G × G => p.1 * p.2) ⁻¹' C)
        ≤ (μN.prod μH) (P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ) := measure_mono hsub
      _ ≤ (μN.prod μH) P + (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ := measure_union_le _ _
      _ < ⊤ := by rw [hprodc, add_zero]; exact hPfin

end PI.ScMuExists.UnitaryGroupMassFormula
