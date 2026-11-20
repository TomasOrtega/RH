import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

open MeasureTheory Filter Set
open scoped symmDiff Topology ENNReal

namespace PositivityTheory.KB.SpectralGap

namespace AlmostEverywhereConstant

variable {S : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
  [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  (μ : Measure S) [μ.IsHaarMeasure]

def tr (g : S) : C(S, S) := ⟨(g * ·), continuous_const_mul g⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_tr (g : S) : ⇑(tr g) = (g * ·) := rfl

/- English proof (translation)
The claim follows from `ContinuousMap.continuous_of_continuous_uncurry _ continuous_mul`.
-/
theorem continuous_tr : Continuous (tr : S → C(S, S)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_mul

/- English proof (translation)
Establish `hc : Tendsto (fun n => tr (x n)) atTop (𝓝 (tr g))` using `(continuous_tr.tendsto g).comp hx`. Establish `key` using `tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) hc (Eventually.of_forall fun n => measurePreserving_mul_left μ (x n)) (measurePreserving_mul_left μ g) hP.nullMeasurableSet hμP`. Simplify `key` using `only [coe_tr]`.
-/
theorem tendsto_pre {x : ℕ → S} {g : S} (hx : Tendsto x atTop (𝓝 g)) {P : Set S}
    (hP : MeasurableSet P) (hμP : μ P ≠ ∞) :
    Tendsto (fun n => μ (((x n * ·) ⁻¹' P) ∆ ((g * ·) ⁻¹' P))) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => tr (x n)) atTop (𝓝 (tr g)) := (continuous_tr.tendsto g).comp hx
  have key := tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) hc
    (Eventually.of_forall fun n => measurePreserving_mul_left μ (x n))
    (measurePreserving_mul_left μ g) hP.nullMeasurableSet hμP
  simpa only [coe_tr] using key

/- English proof (translation)
Apply `isClosed_of_closure_subset` to reduce the goal to its premises. Introduce `g hg`. Take `⟨x, hxS, hx⟩` from `mem_closure_iff_seq_limit.1 hg`. Use `show (g * ·) ⁻¹' T =ᵐ[μ] T`. Rewrite using `[← measure_symmDiff_eq_zero_iff]`.

Establish `key : ∀ K : Set S, IsCompact K → μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K) = 0`. Introduce `K hK`. Take `⟨N, hNc, hN⟩` from `exists_compact_mem_nhds g`. Use `set L : Set S := (fun p : S × S => p.1 * p.2) '' (N ×ˢ K) with hLdef`. Establish `hLc : IsCompact L` using `(hNc.prod hK).image continuous_mul`.

Establish `hPm : MeasurableSet (T ∩ L)` using `hT.inter hLc.measurableSet`. Establish `hPf : μ (T ∩ L) ≠ ∞` using `((measure_mono inter_subset_right).trans_lt hLc.measure_lt_top).ne`. Establish `ev : ∀ᶠ n in atTop, x n ∈ N` using `hx hN`. Establish `tend` using `tendsto_pre μ hx hPm hPf`. Use `le_antisymm ?_ bot_le` and prove the remaining obligations.

Apply `ge_of_tendsto tend` to reduce the goal to its premises. Use `filter_upwards [ev] with n hn`. Establish `h0 : μ (((x n * ·) ⁻¹' T) ∆ T) = 0` using `measure_symmDiff_eq_zero_iff.2 (hxS n)`. Establish `hsub : (((g * ·) ⁻¹' T) ∆ T) ∩ K ⊆ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T)`. Introduce and unpack `y ⟨hyD, hyK⟩`.

Establish `h1 : x n * y ∈ L` using `⟨(x n, y), ⟨hn, hyK⟩, rfl⟩`. Establish `h2 : g * y ∈ L` using `⟨(g, y), ⟨mem_of_mem_nhds hN, hyK⟩, rfl⟩`. Simplify using `only [Set.mem_union, Set.mem_symmDiff, Set.mem_preimage, Set.mem_inter_iff, h1, h2, and_true] at hyD ⊢`. The claim follows by propositional logic. Combine the equalities or inequalities in the displayed calculation.

Establish `hD : ((g * ·) ⁻¹' T) ∆ T = ⋃ n, ((((g * ·) ⁻¹' T) ∆ T) ∩ compactCovering S n)`. Rewrite using `[← inter_iUnion, iUnion_compactCovering, inter_univ]`. Rewrite using `[hD]`. Conclude with `measure_iUnion_null fun n => key _ (isCompact_compactCovering S n)`.
-/
theorem isClosed_stab {T : Set S} (hT : MeasurableSet T) :
    IsClosed {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T} := by
  apply isClosed_of_closure_subset
  intro g hg
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.1 hg
  show (g * ·) ⁻¹' T =ᵐ[μ] T
  rw [← measure_symmDiff_eq_zero_iff]
  have key : ∀ K : Set S, IsCompact K → μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K) = 0 := by
    intro K hK
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds g
    set L : Set S := (fun p : S × S => p.1 * p.2) '' (N ×ˢ K) with hLdef
    have hLc : IsCompact L := (hNc.prod hK).image continuous_mul
    have hPm : MeasurableSet (T ∩ L) := hT.inter hLc.measurableSet
    have hPf : μ (T ∩ L) ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt hLc.measure_lt_top).ne
    have ev : ∀ᶠ n in atTop, x n ∈ N := hx hN
    have tend := tendsto_pre μ hx hPm hPf
    refine le_antisymm ?_ bot_le
    apply ge_of_tendsto tend
    filter_upwards [ev] with n hn
    have h0 : μ (((x n * ·) ⁻¹' T) ∆ T) = 0 := measure_symmDiff_eq_zero_iff.2 (hxS n)
    have hsub : (((g * ·) ⁻¹' T) ∆ T) ∩ K ⊆
        (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T) := by
      rintro y ⟨hyD, hyK⟩
      have h1 : x n * y ∈ L := ⟨(x n, y), ⟨hn, hyK⟩, rfl⟩
      have h2 : g * y ∈ L := ⟨(g, y), ⟨mem_of_mem_nhds hN, hyK⟩, rfl⟩
      simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_preimage, Set.mem_inter_iff, h1, h2,
        and_true] at hyD ⊢
      tauto
    calc μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K)
        ≤ μ ((((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T)) :=
          measure_mono hsub
      _ ≤ μ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) + μ (((x n * ·) ⁻¹' T) ∆ T) :=
          measure_union_le _ _
      _ = μ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) := by rw [h0, add_zero]
  have hD : ((g * ·) ⁻¹' T) ∆ T = ⋃ n, ((((g * ·) ⁻¹' T) ∆ T) ∩ compactCovering S n) := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  rw [hD]
  exact measure_iUnion_null fun n => key _ (isCompact_compactCovering S n)

/- English proof (translation)
Establish `hcl : closure (A : Set S) ⊆ {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T}` using `closure_minimal (fun g hg => h g hg) (isClosed_stab μ hT)`. Rewrite `hcl` using `[hA.closure_eq]`. Conclude with `aeconst_of_forall_preimage_smul_ae_eq S hT.nullMeasurableSet fun g => hcl (mem_univ g)`.
-/
theorem aeconst_set {A : Subgroup S} (hA : Dense (A : Set S)) {T : Set S} (hT : MeasurableSet T)
    (h : ∀ g ∈ A, (g * ·) ⁻¹' T =ᵐ[μ] T) : EventuallyConst T (ae μ) := by
  have hcl : closure (A : Set S) ⊆ {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T} :=
    closure_minimal (fun g hg => h g hg) (isClosed_stab μ hT)
  rw [hA.closure_eq] at hcl
  exact aeconst_of_forall_preimage_smul_ae_eq S hT.nullMeasurableSet fun g => hcl (mem_univ g)

end AlmostEverywhereConstant

/- English proof (translation)
Introduce `S _ _ _ _ _ _ _ _ μ _ A hA u hu hinv`. Use `exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_` and prove the remaining obligations. Introduce `U hU`. Establish `hT : MeasurableSet (u ⁻¹' U)` using `hu hU`. Establish `key` using `AlmostEverywhereConstant.aeconst_set μ hA hT fun g hg => by filter_upwards [hinv g hg] with x hx show (u (g * x) ∈ U) = (u x ∈ U)`.

Rewrite using `[hx]`. Conclude with `eventuallyConst_set.1 key`.
-/
theorem aeConst_holds : AEConst := by
  intro S _ _ _ _ _ _ _ _ μ _ A hA u hu hinv
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_
  intro U hU
  have hT : MeasurableSet (u ⁻¹' U) := hu hU
  have key := AlmostEverywhereConstant.aeconst_set μ hA hT fun g hg => by
    filter_upwards [hinv g hg] with x hx
    show (u (g * x) ∈ U) = (u x ∈ U)
    rw [hx]
  exact eventuallyConst_set.1 key

end PositivityTheory.KB.SpectralGap
