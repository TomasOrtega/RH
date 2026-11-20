import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.SmallUnit

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

/- English proof (translation)
Introduce `hfin`. Establish `hfin' : ({x | x ∈ W ∧ f * x = x} \ {0}).Finite` using `hfin.subset Set.diff_subset`. Establish `hV : ({x | x ∈ W ∧ f * x = x} \ {0})ᶜ ∈ 𝓝 (0 : A)` using `hfin'.isClosed.isOpen_compl.mem_nhds (by simp)`. Take `⟨x, hx, hx0, hfx⟩` from `hf _ (inter_mem hW hV)`. Conclude with `hx.2 ⟨⟨hx.1, hfx⟩, hx0⟩`.
-/
theorem infinite_factor_points {f : A} (hf : NonDiscreteAt f) {W : Set A} (hW : W ∈ 𝓝 (0 : A)) :
    {x | x ∈ W ∧ f * x = x}.Infinite := by
  intro hfin
  have hfin' : ({x | x ∈ W ∧ f * x = x} \ {0}).Finite := hfin.subset Set.diff_subset
  have hV : ({x | x ∈ W ∧ f * x = x} \ {0})ᶜ ∈ 𝓝 (0 : A) :=
    hfin'.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨x, hx, hx0, hfx⟩ := hf _ (inter_mem hW hV)
  exact hx.2 ⟨⟨hx.1, hfx⟩, hx0⟩

/- English proof (translation)
Use `set Q : Set A := (fun w => (1 - f) * w) '' W with hQ`. Establish `hQc : IsCompact Q` using `hWc.image (by fun_prop)`. Assume the negation of the conclusion as `hne`. Use `set K : Set A := (fun p : A × A => p.1 + p.2) '' (W ×ˢ Q) with hK`. Establish `hKc : IsCompact K` using `(hWc.prod hQc).image (by fun_prop)`.

Establish `hKfin : h K ≠ ∞` using `hKc.measure_lt_top.ne`. Take `⟨n, hn⟩` from `ENNReal.exists_nat_mul_gt hne hKfin`. Take `⟨T, hTS, hTc⟩` from `(infinite_factor_points hf hW).exists_subset_card_eq n`. Establish `hdisj : (T : Set A).PairwiseDisjoint (fun p => (fun q => p + q) '' Q)`. Introduce `p hp p' hp' hpp`.

Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨w, -, rfl⟩, rfl⟩ ⟨_, ⟨w', -, rfl⟩, hEq⟩`. Apply `hpp` to reduce the goal to its premises. Establish `hfp : f * p = p` using `(hTS hp).2`. Establish `hfp' : f * p' = p'` using `(hTS hp').2`.

Establish `hz : f * (1 - f) = 0` using `by rw [mul_sub, mul_one, hid, sub_self]`. Use `congrArg (fun t => f * t) hEq` as an intermediate fact. Simplify using `only [mul_add, ← mul_assoc, hz, zero_mul, add_zero, hfp, hfp'] at this`. Conclude with `this.symm`. Establish `hmeas : ∀ p ∈ T, MeasurableSet ((fun q => p + q) '' Q)` using `fun p _ => (hQc.image (by fun_prop)).isClosed.measurableSet`.

Establish `hsum` using `measure_biUnion_finset (μ := h) hdisj hmeas`. Establish `each : ∀ p, h ((fun q => p + q) '' Q) = h Q` using `fun p => by`. Rewrite using `[Set.image_add_left]`. Conclude with `measure_preimage_add h (-p) Q`. Establish `hle : h (⋃ p ∈ T, (fun q => p + q) '' Q) ≤ h K`.

Use `measure_mono (Set.iUnion₂_subset fun p hp => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `⟨(p, q), ⟨(hTS hp).1, hq⟩, rfl⟩`. Rewrite `hle` using `[hsum, Finset.sum_congr rfl (fun p _ => each p), Finset.sum_const, hTc, nsmul_eq_mul]`. Conclude with `absurd hle (not_le.2 hn)`.
-/
theorem measure_complement_image_eq_zero [MeasurableSpace A] [BorelSpace A]
    (h : Measure A) [h.IsAddHaarMeasure] {f : A} (hid : f * f = f) (hf : NonDiscreteAt f)
    {W : Set A} (hWc : IsCompact W) (hW : W ∈ 𝓝 (0 : A)) :
    h ((fun w => (1 - f) * w) '' W) = 0 := by
  set Q : Set A := (fun w => (1 - f) * w) '' W with hQ
  have hQc : IsCompact Q := hWc.image (by fun_prop)
  by_contra hne
  set K : Set A := (fun p : A × A => p.1 + p.2) '' (W ×ˢ Q) with hK
  have hKc : IsCompact K := (hWc.prod hQc).image (by fun_prop)
  have hKfin : h K ≠ ∞ := hKc.measure_lt_top.ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hne hKfin
  obtain ⟨T, hTS, hTc⟩ := (infinite_factor_points hf hW).exists_subset_card_eq n
  have hdisj : (T : Set A).PairwiseDisjoint (fun p => (fun q => p + q) '' Q) := by
    intro p hp p' hp' hpp
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩ ⟨_, ⟨w', -, rfl⟩, hEq⟩
    apply hpp
    have hfp : f * p = p := (hTS hp).2
    have hfp' : f * p' = p' := (hTS hp').2
    have hz : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hid, sub_self]
    have := congrArg (fun t => f * t) hEq
    simp only [mul_add, ← mul_assoc, hz, zero_mul, add_zero, hfp, hfp'] at this
    exact this.symm
  have hmeas : ∀ p ∈ T, MeasurableSet ((fun q => p + q) '' Q) := fun p _ =>
    (hQc.image (by fun_prop)).isClosed.measurableSet
  have hsum := measure_biUnion_finset (μ := h) hdisj hmeas
  have each : ∀ p, h ((fun q => p + q) '' Q) = h Q := fun p => by
    rw [Set.image_add_left]
    exact measure_preimage_add h (-p) Q
  have hle : h (⋃ p ∈ T, (fun q => p + q) '' Q) ≤ h K := by
    refine measure_mono (Set.iUnion₂_subset fun p hp => ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(p, q), ⟨(hTS hp).1, hq⟩, rfl⟩
  rw [hsum, Finset.sum_congr rfl (fun p _ => each p), Finset.sum_const, hTc, nsmul_eq_mul] at hle
  exact absurd hle (not_le.2 hn)

/- English proof (translation)
Establish `hn : IsOpen ((fun p : A × A × A => p.2.1 + p.1 * p.2.2) ⁻¹' O)` using `hO.preimage (by fun_prop)`. Take `⟨u, v, hu, -, h0u, hQWv, huv⟩` from `generalized_tube_lemma (isCompact_singleton (x := (0 : A))) (hQ.prod hW) hn (by`. Introduce and unpack `⟨x, q, w⟩ ⟨hx, hq, hw⟩`. Establish `hx0 : x = 0` using `hx`. Simplify `hQO hq)` using `[hx0]`.

Conclude with `⟨u, hu.mem_nhds (h0u rfl), fun x hx q hq w hw => huv (Set.mk_mem_prod hx (show (q, w) ∈ v from hQWv ⟨hq, hw⟩))⟩`.
-/
theorem exists_nhds_add_mul_subset {Q W O : Set A} (hQ : IsCompact Q) (hW : IsCompact W)
    (hO : IsOpen O) (hQO : Q ⊆ O) :
    ∃ N ∈ 𝓝 (0 : A), ∀ x ∈ N, ∀ q ∈ Q, ∀ w ∈ W, q + x * w ∈ O := by
  have hn : IsOpen ((fun p : A × A × A => p.2.1 + p.1 * p.2.2) ⁻¹' O) :=
    hO.preimage (by fun_prop)
  obtain ⟨u, v, hu, -, h0u, hQWv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A)))
    (hQ.prod hW) hn (by
      rintro ⟨x, q, w⟩ ⟨hx, hq, hw⟩
      have hx0 : x = 0 := hx
      simpa [hx0] using hQO hq)
  exact ⟨u, hu.mem_nhds (h0u rfl), fun x hx q hq w hw => huv (Set.mk_mem_prod hx (show (q, w) ∈ v from hQWv ⟨hq, hw⟩))⟩

end GlobalTheory.CompanionTheory.NullFr.SmallUnit

namespace GlobalTheory.CompanionTheory.NullFr

open SmallUnit in

/- English proof (translation)
Take `⟨W, hWc, hW⟩` from `exists_compact_mem_nhds (0 : A)`. Set `h : Measure A` to `Measure.addHaar`. Establish `hWpos : 0 < h W` using `Measure.measure_pos_of_mem_nhds h hW`. Establish `hWfin : h W ≠ ∞` using `hWc.measure_lt_top.ne`. Use `set Q : Set A := (fun w => (1 - f) * w) '' W with hQdef`.

Establish `hQc : IsCompact Q` using `hWc.image (by fun_prop)`. Establish `hQ0 : h Q = 0` using `measure_complement_image_eq_zero h hfi.idem hnd hWc hW`. Establish `hεW : h Q < (ε : ℝ≥0∞) * h W`. Rewrite using `[hQ0]`. Conclude with `ENNReal.mul_pos (by exact_mod_cast hε.ne') hWpos.ne' |>.bot_lt`.

Take `⟨O, hQO, hOo, hOlt⟩` from `Q.exists_isOpen_lt_of_lt _ hεW`. Take `⟨N, hN, hNO⟩` from `exists_nhds_add_mul_subset hQc hWc hOo hQO`. Take `⟨x, ⟨hxN, hxV⟩, hx0, hfx⟩` from `hnd _ (inter_mem hN hV)`. Take `⟨y, hy⟩` from `hfi.inv x (by rwa [hfx])`. Rewrite `hy` using `[hfx]`.

Establish `hz : f * (1 - f) = 0` using `by rw [mul_sub, mul_one, hfi.idem, sub_self]`. Establish `hzz : (1 - f) * (1 - f) = 1 - f`. Rewrite using `[sub_mul, one_mul, hz, sub_zero]`. Establish `hxz : (1 - f) * x = 0` using `by rw [← hfx, ← mul_assoc, mul_comm (1 - f), hz, zero_mul]`. Establish `huv : (1 - f + x) * (1 - f + f * y) = 1`.

Establish `e : (1 - f + x) * (1 - f + f * y) = (1 - f) * (1 - f) + (f * (1 - f)) * y + (1 - f) * x + (f * x) * y` using `by ring`. Rewrite using `[e, hzz, hz, hxz, hfx, hy]`. Expand and normalize the polynomial expressions, which then agree. Set `u : Aˣ` to `⟨1 - f + x, 1 - f + f * y, huv, by rw [mul_comm]; exact huv⟩`. Establish `hu : (u : A) = 1 - f + x` using `rfl`.

Use `⟨u, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, mul_add, hzz, hxz, add_zero]`. Rewrite using `[hu, mul_add, hz, zero_add, hfx]`. Conclude with `hxV`. Establish `hmap` using `hmd h inferInstance u⁻¹`.

Establish `hWm : MeasurableSet W` using `hWc.isClosed.measurableSet`. Establish `hg : Measurable (fun z : A => ((u⁻¹ : Aˣ) : A) * z)` using `(by fun_prop : Continuous _).measurable`. Establish `hpre : h ((fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W) = (md u : ℝ≥0∞) * h W`. Rewrite using `[← Measure.map_apply hg hWm, hmap, Measure.smul_apply, smul_eq_mul]`. Use `congr 1`.

Establish `hm : md u⁻¹ * md u = 1` using `by rw [← map_mul]; simp`. Establish `: (md u⁻¹ : ℝ≥0∞) * (md u : ℝ≥0∞) = 1` using `by exact_mod_cast hm`. Conclude with `(ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm`. Establish `hsub : (fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W ⊆ O`. Introduce `z hz'`.

Establish `hzw : ((u⁻¹ : Aˣ) : A) * z ∈ W` using `hz'`. Establish `hzeq : z = (1 - f) * (((u⁻¹ : Aˣ) : A) * z) + x * (((u⁻¹ : Aˣ) : A) * z)`. Rewrite using `[← add_mul, ← hu, ← mul_assoc, Units.mul_inv, one_mul]`. Rewrite using `[hzeq]`. Conclude with `hNO x hxN _ ⟨_, hzw, rfl⟩ _ hzw`.

Establish `hlt : (md u : ℝ≥0∞) * h W < (ε : ℝ≥0∞) * h W` using `lt_of_le_of_lt (hpre ▸ measure_mono hsub) hOlt`. Establish `: (md u : ℝ≥0∞) < ε` using `lt_of_mul_lt_mul_right' hlt`. Conclude with `this` after adjusting the coercions.
-/
theorem exists_unit_small_module {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (f : A) (hfi : IsFieldIdem f)
    (hnd : NonDiscreteAt f) (ε : ℝ≥0) (hε : 0 < ε) (V : Set A) (hV : V ∈ 𝓝 (0 : A)) :
    ∃ u : Aˣ, (1 - f) * (u : A) = 1 - f ∧ f * (u : A) ∈ V ∧ md u < ε := by
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (0 : A)
  let h : Measure A := Measure.addHaar
  have hWpos : 0 < h W := Measure.measure_pos_of_mem_nhds h hW
  have hWfin : h W ≠ ∞ := hWc.measure_lt_top.ne
  set Q : Set A := (fun w => (1 - f) * w) '' W with hQdef
  have hQc : IsCompact Q := hWc.image (by fun_prop)
  have hQ0 : h Q = 0 := measure_complement_image_eq_zero h hfi.idem hnd hWc hW
  have hεW : h Q < (ε : ℝ≥0∞) * h W := by
    rw [hQ0]
    exact ENNReal.mul_pos (by exact_mod_cast hε.ne') hWpos.ne' |>.bot_lt
  obtain ⟨O, hQO, hOo, hOlt⟩ := Q.exists_isOpen_lt_of_lt _ hεW
  obtain ⟨N, hN, hNO⟩ := exists_nhds_add_mul_subset hQc hWc hOo hQO
  obtain ⟨x, ⟨hxN, hxV⟩, hx0, hfx⟩ := hnd _ (inter_mem hN hV)
  obtain ⟨y, hy⟩ := hfi.inv x (by rwa [hfx])
  rw [hfx] at hy
  have hz : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hfi.idem, sub_self]
  have hzz : (1 - f) * (1 - f) = 1 - f := by
    rw [sub_mul, one_mul, hz, sub_zero]
  have hxz : (1 - f) * x = 0 := by rw [← hfx, ← mul_assoc, mul_comm (1 - f), hz, zero_mul]
  have huv : (1 - f + x) * (1 - f + f * y) = 1 := by
    have e : (1 - f + x) * (1 - f + f * y) =
        (1 - f) * (1 - f) + (f * (1 - f)) * y + (1 - f) * x + (f * x) * y := by ring
    rw [e, hzz, hz, hxz, hfx, hy]
    ring
  let u : Aˣ := ⟨1 - f + x, 1 - f + f * y, huv, by rw [mul_comm]; exact huv⟩
  have hu : (u : A) = 1 - f + x := rfl
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu, mul_add, hzz, hxz, add_zero]
  · rw [hu, mul_add, hz, zero_add, hfx]
    exact hxV
  · have hmap := hmd h inferInstance u⁻¹
    have hWm : MeasurableSet W := hWc.isClosed.measurableSet
    have hg : Measurable (fun z : A => ((u⁻¹ : Aˣ) : A) * z) := (by fun_prop : Continuous _).measurable
    have hpre : h ((fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W) = (md u : ℝ≥0∞) * h W := by
      rw [← Measure.map_apply hg hWm, hmap, Measure.smul_apply, smul_eq_mul]
      congr 1
      have hm : md u⁻¹ * md u = 1 := by rw [← map_mul]; simp
      have : (md u⁻¹ : ℝ≥0∞) * (md u : ℝ≥0∞) = 1 := by exact_mod_cast hm
      exact (ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm
    have hsub : (fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W ⊆ O := by
      intro z hz'
      have hzw : ((u⁻¹ : Aˣ) : A) * z ∈ W := hz'
      have hzeq : z = (1 - f) * (((u⁻¹ : Aˣ) : A) * z) + x * (((u⁻¹ : Aˣ) : A) * z) := by
        rw [← add_mul, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
      rw [hzeq]
      exact hNO x hxN _ ⟨_, hzw, rfl⟩ _ hzw
    have hlt : (md u : ℝ≥0∞) * h W < (ε : ℝ≥0∞) * h W :=
      lt_of_le_of_lt (hpre ▸ measure_mono hsub) hOlt
    have : (md u : ℝ≥0∞) < ε := lt_of_mul_lt_mul_right' hlt
    exact_mod_cast this

end GlobalTheory.CompanionTheory.NullFr
