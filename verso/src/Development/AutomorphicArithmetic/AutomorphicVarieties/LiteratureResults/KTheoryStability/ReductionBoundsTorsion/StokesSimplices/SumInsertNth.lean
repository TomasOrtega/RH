import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

noncomputable section

open MeasureTheory Set

namespace PositivityTheory.KB.StokesSlices

/- English proof (translation)
Rewrite using `[Fin.sum_univ_succAbove _ i]`. Simplify using `[Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]`.
-/
lemma sum_insertNth' {m : ℕ} (i : Fin (m + 1)) (x : ℝ) (s : Fin m → ℝ) :
    ∑ j, i.insertNth x s j = x + ∑ j, s j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/- English proof (translation)
Simplify using `only [Δ, mem_ofPred_eq, mem_Icc, sum_insertNth', i.forall_iff_succAbove, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hx, hs⟩, h⟩`. Conclude with `⟨⟨hs, by`. Establish `: 0 ≤ ∑ j, s j` using `Finset.sum_nonneg fun j _ => hs j`.

Use the proof step `linarith⟩, hx, by linarith⟩`. Introduce and unpack `⟨⟨hs, _⟩, hx, h⟩`. Conclude with `⟨⟨hx, hs⟩, by linarith⟩`.
-/
lemma mem_Δ_insertNth {m : ℕ} (i : Fin (m + 1)) (x : ℝ) (s : Fin m → ℝ) :
    i.insertNth x s ∈ Δ (m + 1) ↔ s ∈ Δ m ∧ x ∈ Icc 0 (1 - ∑ j, s j) := by
  simp only [Δ, mem_ofPred_eq, mem_Icc, sum_insertNth', i.forall_iff_succAbove,
    Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  constructor
  · rintro ⟨⟨hx, hs⟩, h⟩
    exact ⟨⟨hs, by
      have : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs j
      linarith⟩, hx, by linarith⟩
  · rintro ⟨⟨hs, _⟩, hx, h⟩
    exact ⟨⟨hx, hs⟩, by linarith⟩

/- English proof (translation)
Establish `h1 : IsClosed {t : Fin m → ℝ | ∀ j, 0 ≤ t j}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)`. Establish `h2 : IsClosed {t : Fin m → ℝ | ∑ j, t j ≤ 1}` using `isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const`. Conclude with `h1.inter h2`.
-/
lemma isClosed_Δ (m : ℕ) : IsClosed (Δ m) := by
  have h1 : IsClosed {t : Fin m → ℝ | ∀ j, 0 ≤ t j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have h2 : IsClosed {t : Fin m → ℝ | ∑ j, t j ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
  exact h1.inter h2

/- English proof (translation)
Use `(isCompact_Icc : IsCompact (Set.Icc (0 : Fin m → ℝ) 1)).of_isClosed_subset (isClosed_Δ m) ?_` and prove the remaining obligations. Introduce and unpack `t ⟨h0, h1⟩`. Use `⟨fun j => h0 j, fun j => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma isCompact_Δ (m : ℕ) : IsCompact (Δ m) := by
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : Fin m → ℝ) 1)).of_isClosed_subset (isClosed_Δ m) ?_
  rintro t ⟨h0, h1⟩
  refine ⟨fun j => h0 j, fun j => ?_⟩
  calc t j ≤ ∑ k, t k := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)
    _ ≤ 1 := h1

/- English proof (translation)
The claim follows from `(isClosed_Δ m).measurableSet`.
-/
lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := (isClosed_Δ m).measurableSet

/- English proof (translation)
Use `ContinuousOn.integrableOn_compact (isCompact_Δ m) ?_` and prove the remaining obligations. Establish `hcont : Continuous (fun s : Fin m → ℝ => (i.insertNth (c s) s : Fin (m + 1) → ℝ))` using `Continuous.finInsertNth i hc continuous_id`. Use `hG.comp hcont.continuousOn ?_` and prove the remaining obligations. Introduce `s hs`. Conclude with `hΔW ((mem_Δ_insertNth i _ _).2 ⟨hs, hc0 s hs, hc1 s hs⟩)`.
-/
lemma integrableOn_Δ_insertNth {m : ℕ} (i : Fin (m + 1)) (G : (Fin (m + 1) → ℝ) → ℝ)
    (W : Set (Fin (m + 1) → ℝ)) (hΔW : Δ (m + 1) ⊆ W) (hG : ContinuousOn G W)
    (c : (Fin m → ℝ) → ℝ) (hc : Continuous c) (hc0 : ∀ s ∈ Δ m, 0 ≤ c s)
    (hc1 : ∀ s ∈ Δ m, c s ≤ 1 - ∑ j, s j) :
    IntegrableOn (fun s => G (i.insertNth (c s) s)) (Δ m) := by
  refine ContinuousOn.integrableOn_compact (isCompact_Δ m) ?_
  have hcont : Continuous (fun s : Fin m → ℝ => (i.insertNth (c s) s : Fin (m + 1) → ℝ)) :=
    Continuous.finInsertNth i hc continuous_id
  refine hG.comp hcont.continuousOn ?_
  intro s hs
  exact hΔW ((mem_Δ_insertNth i _ _).2 ⟨hs, hc0 s hs, hc1 s hs⟩)

/- English proof (translation)
Introduce `m i G D W hW hΔW hG hD hderiv`. Use `set e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm with he_def`. Establish `hem : MeasurePreserving e` using `(volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _`. Establish `he : ∀ p : ℝ × (Fin m → ℝ), e p = i.insertNth p.1 p.2` using `fun p => rfl`. Establish `hDint : IntegrableOn D (Δ (m + 1))` using `(hD.mono hΔW).integrableOn_compact (isCompact_Δ _)`.

Establish `hS : MeasurableSet (e ⁻¹' Δ (m + 1))` using `e.measurable (measurableSet_Δ _)`. Establish `hFint : IntegrableOn (fun p => D (e p)) (e ⁻¹' Δ (m + 1)) (volume.prod volume)`. Rewrite using `[← Measure.volume_eq_prod]`. Conclude with `(hem.integrableOn_comp_preimage e.measurableEmbedding).2 hDint`. Rewrite using `[← hem.map_eq, setIntegral_map_equiv, Measure.volume_eq_prod, ← integral_indicator hS, integral_prod_symm _ ((integrable_indicator_iff hS).2 hFint)]`.

Establish `hA` using `integrableOn_Δ_insertNth i G W hΔW hG (fun s => 1 - ∑ j, s j) (continuous_const.sub (continuous_finset_sum _ fun j _ => continuous_apply j)) (fun s hs => by have := hs.2; linarith) (fun s hs => le_rfl)`. Establish `hB` using `integrableOn_Δ_insertNth i G W hΔW hG (fun _ => 0) continuous_const (fun s hs => le_rfl) (fun s hs => by have := hs.2; linarith)`. Rewrite using `[← integral_sub hA hB, ← integral_indicator (measurableSet_Δ m)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Distinguish the cases in `hs : s ∈ Δ m`.

Rewrite using `[Set.indicator_of_mem hs]`. Establish `ha : 0 ≤ 1 - ∑ j, s j` using `by have := hs.2; linarith`. Establish `h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) = (Icc 0 (1 - ∑ j, s j)).indicator (fun x => D (i.insertNth x s)) x`. Introduce `x`. Distinguish the cases in `hx : x ∈ Icc 0 (1 - ∑ j, s j)`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem]`. Rewrite using `[he]`. Use `show e (x, s) ∈ Δ (m + 1)`. Rewrite using `[he]`. Conclude with `(mem_Δ_insertNth i x s).2 ⟨hs, hx⟩`.

Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem] show e (x, s) ∉ Δ (m + 1)`. Rewrite using `[he]`. Conclude with `fun h => hx ((mem_Δ_insertNth i x s).1 h).2`. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]`.

Establish `hcs : Continuous fun x : ℝ => Fin.insertNth (α` using `fun _ => ℝ) i x s := by fun_prop`. Establish `hin : ∀ x ∈ Icc 0 (1 - ∑ j, s j), i.insertNth x s ∈ W` using `fun x hx => hΔW ((mem_Δ_insertNth i x s).2 ⟨hs, hx⟩)`. Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => G (i.insertNth x s))` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Set.uIcc_of_le ha]`.

Use `hderiv _ (hin x hx)` as an intermediate fact. Simplify `this` using `[Fin.update_insertNth, Fin.insertNth_apply_same]`. Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Rewrite using `[Set.uIcc_of_le ha]`. Conclude with `hD.comp hcs.continuousOn hin`.

Rewrite using `[Set.indicator_of_notMem hs]`. Establish `h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) = 0`. Introduce `x`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Use `show e (x, s) ∉ Δ (m + 1)`.

Rewrite using `[he]`. Conclude with `fun h => hs ((mem_Δ_insertNth i x s).1 h).1`. Repeatedly rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
theorem subSlice : SubSlice := by
  intro m i G D W hW hΔW hG hD hderiv
  set e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm with he_def
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _
  have he : ∀ p : ℝ × (Fin m → ℝ), e p = i.insertNth p.1 p.2 := fun p => rfl
  have hDint : IntegrableOn D (Δ (m + 1)) :=
    (hD.mono hΔW).integrableOn_compact (isCompact_Δ _)
  have hS : MeasurableSet (e ⁻¹' Δ (m + 1)) := e.measurable (measurableSet_Δ _)
  have hFint : IntegrableOn (fun p => D (e p)) (e ⁻¹' Δ (m + 1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hDint
  rw [← hem.map_eq, setIntegral_map_equiv, Measure.volume_eq_prod,
    ← integral_indicator hS, integral_prod_symm _ ((integrable_indicator_iff hS).2 hFint)]
  have hA := integrableOn_Δ_insertNth i G W hΔW hG (fun s => 1 - ∑ j, s j)
    (continuous_const.sub (continuous_finset_sum _ fun j _ => continuous_apply j))
    (fun s hs => by have := hs.2; linarith) (fun s hs => le_rfl)
  have hB := integrableOn_Δ_insertNth i G W hΔW hG (fun _ => 0) continuous_const
    (fun s hs => le_rfl) (fun s hs => by have := hs.2; linarith)
  rw [← integral_sub hA hB, ← integral_indicator (measurableSet_Δ m)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Δ m
  · rw [Set.indicator_of_mem hs]
    have ha : 0 ≤ 1 - ∑ j, s j := by have := hs.2; linarith
    have h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) =
        (Icc 0 (1 - ∑ j, s j)).indicator (fun x => D (i.insertNth x s)) x := by
      intro x
      by_cases hx : x ∈ Icc 0 (1 - ∑ j, s j)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
        · rw [he]
        · show e (x, s) ∈ Δ (m + 1)
          rw [he]
          exact (mem_Δ_insertNth i x s).2 ⟨hs, hx⟩
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        show e (x, s) ∉ Δ (m + 1)
        rw [he]
        exact fun h => hx ((mem_Δ_insertNth i x s).1 h).2
    simp_rw [h1]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ha]
    have hcs : Continuous fun x : ℝ => Fin.insertNth (α := fun _ => ℝ) i x s := by
      fun_prop
    have hin : ∀ x ∈ Icc 0 (1 - ∑ j, s j), i.insertNth x s ∈ W :=
      fun x hx => hΔW ((mem_Δ_insertNth i x s).2 ⟨hs, hx⟩)
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => G (i.insertNth x s))
    · intro x hx
      rw [Set.uIcc_of_le ha] at hx
      have := hderiv _ (hin x hx)
      simpa [Fin.update_insertNth, Fin.insertNth_apply_same] using this
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ha]
      exact hD.comp hcs.continuousOn hin
  · rw [Set.indicator_of_notMem hs]
    have h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) = 0 := by
      intro x
      apply Set.indicator_of_notMem
      show e (x, s) ∉ Δ (m + 1)
      rw [he]
      exact fun h => hs ((mem_Δ_insertNth i x s).1 h).1
    simp_rw [h1]
    simp

end PositivityTheory.KB.StokesSlices
