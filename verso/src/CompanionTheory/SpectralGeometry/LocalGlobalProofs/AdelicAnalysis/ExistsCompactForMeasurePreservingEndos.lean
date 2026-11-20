import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

/- English proof (translation)
Introduce `V _ _ _ _ _ _ _ _ μ _ htop Λ _ _ j C hC hcov`. Establish `hCfin : μ C < ⊤` using `hC.measure_lt_top`. Take `⟨K, -, hKc, hK⟩` from `isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C) (by rw [htop]; exact hCfin)`. Use `⟨(fun p : V × V => p.1 - p.2) '' (K ×ˢ K), (hKc.prod hKc).image (continuous_fst.sub continuous_snd), fun e he hμ => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hno`.

Use `push_neg at hno`. Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`. Establish `hem : Measurable e` using `he.measurable`. Establish `hAm : MeasurableSet (e ⁻¹' K)` using `hem hKm`. Establish `hμA : μ (e ⁻¹' K) = μ K`.

Establish `h` using `Measure.map_apply (μ := μ) hem hKm`. Rewrite `h` using `[hμ]`. Conclude with `h.symm`. Set `S : Λ → Set V` to `fun l => ((fun x => x + j l) ⁻¹' (e ⁻¹' K)) ∩ C`. Establish `hCm : MeasurableSet C` using `hC.isClosed.measurableSet`.

Establish `hSm : ∀ l, MeasurableSet (S l)` using `fun l => (hAm.preimage (measurable_add_const (j l))).inter hCm`. Establish `hdisj : Pairwise (Function.onFun Disjoint S)`. Introduce `l l' hll`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, -⟩ ⟨hx', -⟩`.

Establish `hne : l - l' ≠ 0` using `sub_ne_zero.2 hll`. Use `hno _ hne ?_` and prove the remaining obligations. Establish `hx1 : e (x + j l) ∈ K` using `hx`. Establish `hx2 : e (x + j l') ∈ K` using `hx'`. Establish `: e (j (l - l')) = e (x + j l) - e (x + j l')`.

Rewrite using `[← map_sub, map_sub j]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `⟨(e (x + j l), e (x + j l')), ⟨hx1, hx2⟩, rfl⟩`.

Establish `hcover : e ⁻¹' K ⊆ ⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)`. Introduce `y hy`. Take `⟨l, hl⟩` from `hcov y`. Conclude with `Set.mem_iUnion.2 ⟨l, hy, hl⟩`. Establish `hpiece : ∀ l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) = μ (S l)`.

Introduce `l`. Establish `hS : S l = (fun x => x + j l) ⁻¹' ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C))`. Use extensionality with `x`. Simplify using `[S]`. Rewrite using `[hS, measure_preimage_add_right]`.

Establish `hle : μ K ≤ μ C`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd hK (not_lt.2 hle)`.
-/
theorem lattice_pigeonhole_measure_preserving :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ →
      ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C →
        (∀ y, ∃ l, y - j l ∈ C) →
        ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ →
          ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  intro V _ _ _ _ _ _ _ _ μ _ htop Λ _ _ j C hC hcov
  have hCfin : μ C < ⊤ := hC.measure_lt_top
  obtain ⟨K, -, hKc, hK⟩ :=
    isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C) (by rw [htop]; exact hCfin)
  refine ⟨(fun p : V × V => p.1 - p.2) '' (K ×ˢ K),
    (hKc.prod hKc).image (continuous_fst.sub continuous_snd), fun e he hμ => ?_⟩
  by_contra hno
  push_neg at hno
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hem : Measurable e := he.measurable
  have hAm : MeasurableSet (e ⁻¹' K) := hem hKm
  have hμA : μ (e ⁻¹' K) = μ K := by
    have h := Measure.map_apply (μ := μ) hem hKm
    rw [hμ] at h
    exact h.symm

  let S : Λ → Set V := fun l => ((fun x => x + j l) ⁻¹' (e ⁻¹' K)) ∩ C
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hSm : ∀ l, MeasurableSet (S l) := fun l =>
    (hAm.preimage (measurable_add_const (j l))).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro l l' hll
    refine Set.disjoint_left.2 ?_
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    have hne : l - l' ≠ 0 := sub_ne_zero.2 hll
    refine hno _ hne ?_
    have hx1 : e (x + j l) ∈ K := hx
    have hx2 : e (x + j l') ∈ K := hx'
    have : e (j (l - l')) = e (x + j l) - e (x + j l') := by
      rw [← map_sub, map_sub j]
      congr 1
      abel
    rw [this]
    exact ⟨(e (x + j l), e (x + j l')), ⟨hx1, hx2⟩, rfl⟩
  have hcover : e ⁻¹' K ⊆ ⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C) := by
    intro y hy
    obtain ⟨l, hl⟩ := hcov y
    exact Set.mem_iUnion.2 ⟨l, hy, hl⟩
  have hpiece : ∀ l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) = μ (S l) := by
    intro l
    have hS : S l = (fun x => x + j l) ⁻¹' ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := by
      ext x
      simp [S]
    rw [hS, measure_preimage_add_right]
  have hle : μ K ≤ μ C := by
    calc μ K = μ (e ⁻¹' K) := hμA.symm
      _ ≤ μ (⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := measure_mono hcover
      _ ≤ ∑' l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := measure_iUnion_le _
      _ = ∑' l, μ (S l) := by simp_rw [hpiece]
      _ = μ (⋃ l, S l) := (measure_iUnion hdisj hSm).symm
      _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Adelic
