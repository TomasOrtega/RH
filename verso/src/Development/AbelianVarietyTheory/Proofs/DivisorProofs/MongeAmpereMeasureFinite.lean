import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `e X _ _ _ _ _ A Φ O hO hV`. Distinguish the cases in `hne : Nonempty (ChartPartition A)`. Use `swap`. Unfold `maMeasure`. Rewrite using `[dif_neg hne]`.

Simplify using the standard rewrite rules. Rewrite using `[maMeasure_eq_sum A Φ hne, Measure.coe_finsetSum, Finset.sum_apply]`. Use `ENNReal.sum_lt_top.mpr fun j _ => ?_` and prove the remaining obligations. Use `set P := hne.some`. Use `set ch := A.chart j with hch`.

Establish `hTm : MeasurableSet ch.target` using `ch.open_target.measurableSet`. Establish `hsm : AEMeasurable ch.symm (volume.restrict ch.target)` using `ch.continuousOn_symm.aemeasurable hTm`. Unfold `chartMeasure`. Rewrite using `[Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hO.measurableSet, withDensity_apply' _ _, Measure.restrict_restrict' hTm]`. Establish `hZ : IsCompact (tsupport (P.χ j))` using `(isClosed_tsupport _).isCompact`.

Establish `hsrc : ∀ x ∈ tsupport (P.χ j), x ∈ ch.source` using `fun x hx => P.tsupport_subset j hx`. Use `choose V hVo hxV hVf using fun (x : X) (hx : x ∈ tsupport (P.χ j)) => hV j x (hsrc x hx)`. Take `⟨t, ht⟩` from `hZ.elim_nhds_subcover' (fun x hx => V x hx) (fun x hx => (hVo x hx).mem_nhds (hxV x hx))`. Set `S : ↥(tsupport (P.χ j)) → Set (Fin e → ℂ)` to `fun (x : ↥(tsupport (P.χ j))) => ch.target ∩ ch.symm ⁻¹' (V x.1 x.2 ∩ O)`. Establish `hSo : ∀ x, IsOpen (S x)` using `fun x => ch.isOpen_inter_preimage_symm ((hVo x.1 x.2).inter hO)`.

Set `W` to `⋃ x : ↥t, S x.1`. Establish `hWm : MeasurableSet W` using `(isOpen_iUnion fun (x : ↥t) => hSo x.1).measurableSet`. Establish `hS'm : MeasurableSet (ch.symm ⁻¹' O ∩ ch.target)`. Rewrite using `[Set.inter_comm]`. Conclude with `(ch.isOpen_inter_preimage_symm hO).measurableSet`.

Establish `hpt : ∀ y ∈ ch.symm ⁻¹' O ∩ ch.target, ENNReal.ofReal (P.χ j (ch.symm y) * locDens A Φ j y) ≤ W.indicator (fun y => ENNReal.ofReal (locDens A Φ j y)) y`. Introduce `y hy`. Distinguish the cases in `h0 : P.χ j (ch.symm y) = 0`. Simplify using `[h0]`. Establish `hz : ch.symm y ∈ tsupport (P.χ j)` using `subset_tsupport _ h0`.

Establish `hcov` using `ht hz`. Simplify using `only [Set.mem_iUnion] at hcov`. Take `⟨x, hxt, hyx⟩` from `hcov`. Establish `hyW : y ∈ W` using `Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hy.2, hyx, hy.1⟩`. Rewrite using `[Set.indicator_of_mem hyW, ENNReal.ofReal_mul (P.nonneg j _)]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem maMeasure_lt_top_of_locally_finite : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (O : Set X), IsOpen O → (∀ (j : Fin A.n) (x : X), x ∈ (A.chart j).source → ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (V ∩ O), ENNReal.ofReal (locDens A Φ j y) < ⊤) → maMeasure A Φ O < ⊤ := by
  intro e X _ _ _ _ _ A Φ O hO hV
  by_cases hne : Nonempty (ChartPartition A)
  swap
  · unfold maMeasure; rw [dif_neg hne]; simp
  rw [maMeasure_eq_sum A Φ hne, Measure.coe_finsetSum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.mpr fun j _ => ?_
  set P := hne.some
  set ch := A.chart j with hch
  have hTm : MeasurableSet ch.target := ch.open_target.measurableSet
  have hsm : AEMeasurable ch.symm (volume.restrict ch.target) :=
    ch.continuousOn_symm.aemeasurable hTm
  unfold chartMeasure
  rw [Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _))
    hO.measurableSet, withDensity_apply' _ _, Measure.restrict_restrict' hTm]
  have hZ : IsCompact (tsupport (P.χ j)) := (isClosed_tsupport _).isCompact
  have hsrc : ∀ x ∈ tsupport (P.χ j), x ∈ ch.source := fun x hx => P.tsupport_subset j hx
  choose V hVo hxV hVf using fun (x : X) (hx : x ∈ tsupport (P.χ j)) => hV j x (hsrc x hx)
  obtain ⟨t, ht⟩ := hZ.elim_nhds_subcover' (fun x hx => V x hx)
    (fun x hx => (hVo x hx).mem_nhds (hxV x hx))
  let S : ↥(tsupport (P.χ j)) → Set (Fin e → ℂ) := fun (x : ↥(tsupport (P.χ j))) => ch.target ∩ ch.symm ⁻¹' (V x.1 x.2 ∩ O)
  have hSo : ∀ x, IsOpen (S x) := fun x => ch.isOpen_inter_preimage_symm ((hVo x.1 x.2).inter hO)
  let W := ⋃ x : ↥t, S x.1
  have hWm : MeasurableSet W := (isOpen_iUnion fun (x : ↥t) => hSo x.1).measurableSet
  have hS'm : MeasurableSet (ch.symm ⁻¹' O ∩ ch.target) := by
    rw [Set.inter_comm]; exact (ch.isOpen_inter_preimage_symm hO).measurableSet
  have hpt : ∀ y ∈ ch.symm ⁻¹' O ∩ ch.target,
      ENNReal.ofReal (P.χ j (ch.symm y) * locDens A Φ j y) ≤
        W.indicator (fun y => ENNReal.ofReal (locDens A Φ j y)) y := by
    intro y hy
    by_cases h0 : P.χ j (ch.symm y) = 0
    · simp [h0]
    have hz : ch.symm y ∈ tsupport (P.χ j) := subset_tsupport _ h0
    have hcov := ht hz
    simp only [Set.mem_iUnion] at hcov
    obtain ⟨x, hxt, hyx⟩ := hcov
    have hyW : y ∈ W := Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hy.2, hyx, hy.1⟩
    rw [Set.indicator_of_mem hyW, ENNReal.ofReal_mul (P.nonneg j _)]
    calc ENNReal.ofReal (P.χ j (ch.symm y)) * ENNReal.ofReal (locDens A Φ j y)
        ≤ 1 * ENNReal.ofReal (locDens A Φ j y) := by
          gcongr; exact ENNReal.ofReal_le_one.mpr (chi_le_one P j _)
      _ = _ := one_mul _
  calc ∫⁻ y in ch.symm ⁻¹' O ∩ ch.target, ENNReal.ofReal (P.χ j (ch.symm y) * locDens A Φ j y)
      ≤ ∫⁻ y in ch.symm ⁻¹' O ∩ ch.target,
          W.indicator (fun y => ENNReal.ofReal (locDens A Φ j y)) y := setLIntegral_mono' hS'm hpt
    _ ≤ ∫⁻ y, W.indicator (fun y => ENNReal.ofReal (locDens A Φ j y)) y := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y in W, ENNReal.ofReal (locDens A Φ j y) := lintegral_indicator hWm _
    _ ≤ ∑' x : ↥t, ∫⁻ y in S x.1, ENNReal.ofReal (locDens A Φ j y) := lintegral_iUnion_le _ _
    _ = ∑ x : ↥t, ∫⁻ y in S x.1, ENNReal.ofReal (locDens A Φ j y) := tsum_fintype _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => hVf x.1.1 x.1.2

end GlobalTheory
