import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Packing

/- English proof (translation)
Take `⟨P₀, hP₀⟩` from `h0`. Establish `hne : {n : ℕ | ∃ P, Q P ∧ P.card = n}.Nonempty` using `⟨P₀.card, P₀, hP₀, rfl⟩`. Establish `hbdd : BddAbove {n : ℕ | ∃ P, Q P ∧ P.card = n}`. Use `⟨B, ?_⟩` and prove the remaining obligations. Introduce and unpack `n ⟨P, hP, rfl⟩`.

Conclude with `hB P hP`. Take `⟨P, hP, hcard⟩` from `Nat.sSup_mem hne hbdd`. Use `⟨P, hP, fun P' hP' => ?_⟩` and prove the remaining obligations. Rewrite using `[hcard]`. Conclude with `le_csSup hbdd ⟨P', hP', rfl⟩`.
-/
theorem exists_max_card {α : Type} (Q : Finset α → Prop) (B : ℕ) (h0 : ∃ P, Q P)
    (hB : ∀ P, Q P → P.card ≤ B) : ∃ P, Q P ∧ ∀ P', Q P' → P'.card ≤ P.card := by
  obtain ⟨P₀, hP₀⟩ := h0
  have hne : {n : ℕ | ∃ P, Q P ∧ P.card = n}.Nonempty := ⟨P₀.card, P₀, hP₀, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ P, Q P ∧ P.card = n} := by
    refine ⟨B, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact hB P hP
  obtain ⟨P, hP, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨P, hP, fun P' hP' => ?_⟩
  rw [hcard]
  exact le_csSup hbdd ⟨P', hP', rfl⟩

/- English proof (translation)
Establish `hc : Continuous fun x : A => (u : A) * x` using `continuous_const.mul continuous_id`. Establish `hinj : Function.Injective fun x : A => (u : A) * x` using `fun x y hxy => by`. Simplify using `using congrArg (fun z => ((u⁻¹ : Aˣ) : A) * z) hxy`. Establish `hKu : IsCompact ((fun x : A => (u : A) * x) '' K)` using `hK.image hc`. Establish `key` using `congrArg (fun μ : Measure A => μ ((fun x : A => (u : A) * x) '' K)) (hmd h inferInstance u)`.

Rewrite `key` using `[Measure.map_apply hc.measurable hKu.measurableSet, Set.preimage_image_eq _ hinj, Measure.smul_apply, smul_eq_mul]`. Establish `hmd0 : ((md u : ℝ≥0) : ℝ≥0∞) ≠ 0`. Establish `h1 : md u * md u⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Introduce `h0`. Rewrite `h0` using `[ENNReal.coe_eq_zero]`.

Rewrite `h1` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1`. Rewrite using `[key, ← mul_assoc, ENNReal.mul_inv_cancel hmd0 ENNReal.coe_ne_top, one_mul]`.
-/
theorem measure_unit_image {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K : Set A} (hK : IsCompact K) :
    h ((fun x : A => (u : A) * x) '' K) = md u * h K := by
  have hc : Continuous fun x : A => (u : A) * x := continuous_const.mul continuous_id
  have hinj : Function.Injective fun x : A => (u : A) * x := fun x y hxy => by
    simpa using congrArg (fun z => ((u⁻¹ : Aˣ) : A) * z) hxy
  have hKu : IsCompact ((fun x : A => (u : A) * x) '' K) := hK.image hc
  have key := congrArg (fun μ : Measure A => μ ((fun x : A => (u : A) * x) '' K))
    (hmd h inferInstance u)
  rw [Measure.map_apply hc.measurable hKu.measurableSet, Set.preimage_image_eq _ hinj,
    Measure.smul_apply, smul_eq_mul] at key
  have hmd0 : ((md u : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    intro h0
    rw [ENNReal.coe_eq_zero] at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  rw [key, ← mul_assoc, ENNReal.mul_inv_cancel hmd0 ENNReal.coe_ne_top, one_mul]

/- English proof (translation)
Establish `hcont : ∀ p : A, Continuous fun x : A => p + (u : A) * x` using `fun p => continuous_const.add (continuous_const.mul continuous_id)`. Establish `hmT : ∀ p : A, h ((fun x : A => p + (u : A) * x) '' K) = md u * h K`. Introduce `p`. Establish `e : (fun x : A => p + (u : A) * x) '' K = (fun y => -p + y) ⁻¹' ((fun x : A => (u : A) * x) '' K)`. Use extensionality with `y`.

Simplify using `only [Set.mem_image, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, by abel⟩`. Introduce and unpack `⟨x, hx, hxy⟩`.

Conclude with `⟨x, hx, by rw [hxy]; abel⟩`. Rewrite using `[e, measure_preimage_add, GlobalTheory.CompanionTheory.NullFr.Packing.measure_unit_image hmd h u hK]`. Establish `hsub : (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) ⊆ L`. Use `Set.iUnion₂_subset fun p hp => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Conclude with `hL p hp w hw`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl (fun p _ => hmT p), Finset.sum_const, nsmul_eq_mul]`. Use `_ = h (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) := (measure_biUnion_finset (fun p hp q hq hpq => hdisj p hp q hq hpq) (fun p _ => (hK.image (hcont p)).measurableSet)).symm`. Use `_ ≤ h L := measure_mono hsub`.
-/
theorem card_mul_le {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K L : Set A} (hK : IsCompact K) (P : Finset A)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K))
    (hL : ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L) :
    (P.card : ℝ≥0∞) * (md u * h K) ≤ h L := by
  classical
  have hcont : ∀ p : A, Continuous fun x : A => p + (u : A) * x := fun p =>
    continuous_const.add (continuous_const.mul continuous_id)
  have hmT : ∀ p : A, h ((fun x : A => p + (u : A) * x) '' K) = md u * h K := by
    intro p
    have e : (fun x : A => p + (u : A) * x) '' K =
        (fun y => -p + y) ⁻¹' ((fun x : A => (u : A) * x) '' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by abel⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, by rw [hxy]; abel⟩
    rw [e, measure_preimage_add, GlobalTheory.CompanionTheory.NullFr.Packing.measure_unit_image hmd h u hK]
  have hsub : (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) ⊆ L := by
    refine Set.iUnion₂_subset fun p hp => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hL p hp w hw
  calc (P.card : ℝ≥0∞) * (md u * h K)
      = ∑ p ∈ P, h ((fun x : A => p + (u : A) * x) '' K) := by
        rw [Finset.sum_congr rfl (fun p _ => hmT p), Finset.sum_const, nsmul_eq_mul]
    _ = h (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) :=
        (measure_biUnion_finset (fun p hp q hq hpq => hdisj p hp q hq hpq)
          (fun p _ => (hK.image (hcont p)).measurableSet)).symm
    _ ≤ h L := measure_mono hsub

/- English proof (translation)
Introduce `A _ _ _ _ _ _ _ _ md hmd f _ C U hC hU`. Establish `hU' : U ∈ 𝓝 ((0 : A) - 0)` using `by rwa [sub_zero]`. Establish `h0 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A))` using `continuous_sub.tendsto ((0 : A), (0 : A)) hU'`. Take `⟨W₁, hW₁, W₂, hW₂, hW⟩` from `mem_nhds_prod_iff.1 h0`. Take `⟨K, hK0, hKW, hK⟩` from `local_compact_nhds (Filter.inter_mem hW₁ hW₂)`.

Establish `hKU : ∀ a ∈ K, ∀ b ∈ K, a - b ∈ U` using `fun a ha b hb => hW (Set.mk_mem_prod (hKW ha).1 (hKW hb).2)`. Take `⟨V, hV0, -, hV⟩` from `local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : A))`. Take `⟨L, hLdef⟩ : ∃ L : Set A, L = (fun q : A × A × A => q.1 + q.2.1 * q.2.2 + (1 - f) * q.2.2) '' (C ×ˢ V ×ˢ K)` from `⟨_, rfl⟩`. Establish `hLc : IsCompact L`. Rewrite using `[hLdef]`.

Conclude with `(hC.prod (hV.prod hK)).image (by fun_prop)`. Take `⟨μ, hμ⟩ : ∃ μ : Measure A, μ.IsAddHaarMeasure` from `⟨Measure.addHaar, inferInstance⟩`. Establish `hKpos : 0 < μ K` using `Measure.measure_pos_of_mem_nhds μ hK0`. Establish `hKfin : μ K < ⊤` using `hK.measure_lt_top`. Establish `hLfin : μ L < ⊤` using `hLc.measure_lt_top`.

Use `⟨(μ L / μ K).toNNReal, V, hV0, ?_⟩` and prove the remaining obligations. Introduce `u hu1 hfu`. Establish `hmd0 : md u ≠ 0`. Introduce `h0`. Establish `h1 : md u * md u⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`.

Rewrite `h1` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1`. Establish `hm0 : (md u : ℝ≥0∞) * μ K ≠ 0` using `mul_ne_zero (by exact_mod_cast hmd0) hKpos.ne'`. Establish `hmtop : (md u : ℝ≥0∞) * μ K ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin.ne`. Establish `hLmem : ∀ P : Finset A, (∀ p ∈ P, f * p = p ∧ p ∈ C) → ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L`.

Introduce `P hP p hp w hw`. Rewrite using `[hLdef]`. Use `⟨(p, f * u, w), ⟨(hP p hp).2, hfu, hw⟩, ?_⟩` and prove the remaining obligations. Use `show p + f * u * w + (1 - f) * w = p + u * w`. Rewrite using `[← hu1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hB : ∀ P : Finset A, ((∀ p ∈ P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)) → P.card ≤ ⌈(μ L / ((md u : ℝ≥0∞) * μ K)).toReal⌉₊`. Introduce `P hP`. Establish `hc` using `GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hP.2 (hLmem P hP.1)`. Establish `h1 : (P.card : ℝ≥0∞) ≤ μ L / ((md u : ℝ≥0∞) * μ K)` using `(ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 hc`.

Establish `h2 : (P.card : ℝ) ≤ (μ L / ((md u : ℝ≥0∞) * μ K)).toReal`. Simplify using `using ENNReal.toReal_mono (ENNReal.div_ne_top hLfin.ne hm0) h1`. Conclude with `h2.trans (Nat.le_ceil _)` after adjusting the coercions. Take `⟨P, ⟨hPC, hPdisj⟩, hmax⟩` from `GlobalTheory.CompanionTheory.NullFr.Packing.exists_max_card (hB := hB) (h0 := ⟨∅, by simp⟩)`. Use `⟨P, hPC, ?_, ?_⟩` and prove the remaining obligations.

Establish `hc` using `GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hPdisj (hLmem P hPC)`. Establish `h2 : (((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞) ≤ μ L / μ K`. Rewrite using `[ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKfin.ne)]`. Use `push_cast`. Rewrite using `[mul_assoc]`.

Conclude with `hc`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.toNNReal_coe]`. Use `_ ≤ (μ L / μ K).toNNReal := ENNReal.toNNReal_mono (ENNReal.div_ne_top hLfin.ne hKpos.ne') h2`. Introduce `c hc hfc`.

Distinguish the cases in `hcP : c ∈ P`. Conclude with `⟨c, hcP, 0, mem_of_mem_nhds hU, by simp, by simp⟩`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hpc⟩ : ∃ p ∈ P, ¬ Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => c + (u : A) * x) '' K) := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hQ : (∀ p ∈ insert c P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ insert c P, ∀ q ∈ insert c P, p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)`. Use `⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hp with rfl | hp'` into its components or cases. Conclude with `⟨hfc, hc⟩`. Conclude with `hPC p hp'`.

Apply the tactic sequence `rcases Finset.mem_insert.1 hp with rfl | hp' <;>`. Break down `Finset.mem_insert.1 hq with rfl | hq'` into its components or cases. Conclude with `absurd rfl hpq`. Conclude with `(hcon q hq').symm`. Conclude with `hcon p hp'`.

Conclude with `hPdisj p hp' q hq' hpq`. Establish `hle` using `hmax _ hQ`. Rewrite `hle` using `[Finset.card_insert_of_notMem hcP]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, ⟨k₁, hk₁, hx₁⟩, ⟨k₂, hk₂, hx₂⟩⟩` from `Set.not_disjoint_iff.1 hpc`.

Establish `hx₁' : p + (u : A) * k₁ = x` using `hx₁`. Establish `hx₂' : c + (u : A) * k₂ = x` using `hx₂`. Establish `hw : (u : A) * (k₁ - k₂) = c - p` using `by linear_combination hx₁' - hx₂'`. Establish `hfp : f * p = p` using `(hPC p hp).1`. Use `⟨p, hp, k₁ - k₂, hKU k₁ hk₁ k₂ hk₂, ?_, by rw [hw]; ring⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem net : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (md : Aˣ →* ℝ≥0) (_ : IsHaarMod md) (f : A) (_ : f * f = f) (C U : Set A) (_ : IsCompact C) (_ : U ∈ 𝓝 (0 : A)),
    ∃ (κ : ℝ≥0) (V : Set A), V ∈ 𝓝 (0 : A) ∧ ∀ u : Aˣ, (1 - f) * (u : A) = 1 - f → f * (u : A) ∈ V →
      ∃ N : Finset A, (∀ p ∈ N, f * p = p ∧ p ∈ C) ∧ (N.card : ℝ≥0) * md u ≤ κ ∧
        ∀ c ∈ C, f * c = c → ∃ p ∈ N, ∃ w ∈ U, f * w = w ∧ c = p + u * w := by
  intro A _ _ _ _ _ _ _ _ md hmd f _ C U hC hU
  classical
  have hU' : U ∈ 𝓝 ((0 : A) - 0) := by rwa [sub_zero]
  have h0 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_sub.tendsto ((0 : A), (0 : A)) hU'
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨K, hK0, hKW, hK⟩ := local_compact_nhds (Filter.inter_mem hW₁ hW₂)
  have hKU : ∀ a ∈ K, ∀ b ∈ K, a - b ∈ U := fun a ha b hb =>
    hW (Set.mk_mem_prod (hKW ha).1 (hKW hb).2)
  obtain ⟨V, hV0, -, hV⟩ := local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : A))
  obtain ⟨L, hLdef⟩ : ∃ L : Set A,
      L = (fun q : A × A × A => q.1 + q.2.1 * q.2.2 + (1 - f) * q.2.2) '' (C ×ˢ V ×ˢ K) :=
    ⟨_, rfl⟩
  have hLc : IsCompact L := by
    rw [hLdef]
    exact (hC.prod (hV.prod hK)).image (by fun_prop)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure A, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hKpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK0
  have hKfin : μ K < ⊤ := hK.measure_lt_top
  have hLfin : μ L < ⊤ := hLc.measure_lt_top
  refine ⟨(μ L / μ K).toNNReal, V, hV0, ?_⟩
  intro u hu1 hfu
  have hmd0 : md u ≠ 0 := by
    intro h0
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hm0 : (md u : ℝ≥0∞) * μ K ≠ 0 := mul_ne_zero (by exact_mod_cast hmd0) hKpos.ne'
  have hmtop : (md u : ℝ≥0∞) * μ K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin.ne
  have hLmem : ∀ P : Finset A, (∀ p ∈ P, f * p = p ∧ p ∈ C) →
      ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L := by
    intro P hP p hp w hw
    rw [hLdef]
    refine ⟨(p, f * u, w), ⟨(hP p hp).2, hfu, hw⟩, ?_⟩
    show p + f * u * w + (1 - f) * w = p + u * w
    rw [← hu1]
    ring
  have hB : ∀ P : Finset A, ((∀ p ∈ P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)) →
      P.card ≤ ⌈(μ L / ((md u : ℝ≥0∞) * μ K)).toReal⌉₊ := by
    intro P hP
    have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hP.2 (hLmem P hP.1)
    have h1 : (P.card : ℝ≥0∞) ≤ μ L / ((md u : ℝ≥0∞) * μ K) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 hc
    have h2 : (P.card : ℝ) ≤ (μ L / ((md u : ℝ≥0∞) * μ K)).toReal := by
      simpa using ENNReal.toReal_mono (ENNReal.div_ne_top hLfin.ne hm0) h1
    exact_mod_cast h2.trans (Nat.le_ceil _)
  obtain ⟨P, ⟨hPC, hPdisj⟩, hmax⟩ :=
    GlobalTheory.CompanionTheory.NullFr.Packing.exists_max_card (hB := hB) (h0 := ⟨∅, by simp⟩)
  refine ⟨P, hPC, ?_, ?_⟩
  · have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hPdisj (hLmem P hPC)
    have h2 : (((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞) ≤ μ L / μ K := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKfin.ne)]
      push_cast
      rw [mul_assoc]
      exact hc
    calc (P.card : ℝ≥0) * md u = ((((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞)).toNNReal := by
          rw [ENNReal.toNNReal_coe]
      _ ≤ (μ L / μ K).toNNReal :=
          ENNReal.toNNReal_mono (ENNReal.div_ne_top hLfin.ne hKpos.ne') h2
  · intro c hc hfc
    by_cases hcP : c ∈ P
    · exact ⟨c, hcP, 0, mem_of_mem_nhds hU, by simp, by simp⟩
    · obtain ⟨p, hp, hpc⟩ : ∃ p ∈ P, ¬ Disjoint ((fun x : A => p + (u : A) * x) '' K)
          ((fun x : A => c + (u : A) * x) '' K) := by
        by_contra hcon
        push_neg at hcon
        have hQ : (∀ p ∈ insert c P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ insert c P, ∀ q ∈ insert c P,
            p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K)
              ((fun x : A => q + (u : A) * x) '' K) := by
          refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨hfc, hc⟩
            · exact hPC p hp'
          · rcases Finset.mem_insert.1 hp with rfl | hp' <;>
              rcases Finset.mem_insert.1 hq with rfl | hq'
            · exact absurd rfl hpq
            · exact (hcon q hq').symm
            · exact hcon p hp'
            · exact hPdisj p hp' q hq' hpq
        have hle := hmax _ hQ
        rw [Finset.card_insert_of_notMem hcP] at hle
        omega
      obtain ⟨x, ⟨k₁, hk₁, hx₁⟩, ⟨k₂, hk₂, hx₂⟩⟩ := Set.not_disjoint_iff.1 hpc
      have hx₁' : p + (u : A) * k₁ = x := hx₁
      have hx₂' : c + (u : A) * k₂ = x := hx₂
      have hw : (u : A) * (k₁ - k₂) = c - p := by linear_combination hx₁' - hx₂'
      have hfp : f * p = p := (hPC p hp).1
      refine ⟨p, hp, k₁ - k₂, hKU k₁ hk₁ k₂ hk₂, ?_, by rw [hw]; ring⟩
      calc f * (k₁ - k₂) = ((u⁻¹ : Aˣ) : A) * ((u : A) * (f * (k₁ - k₂))) := by simp
        _ = ((u⁻¹ : Aˣ) : A) * (f * ((u : A) * (k₁ - k₂))) := by ring
        _ = ((u⁻¹ : Aˣ) : A) * ((u : A) * (k₁ - k₂)) := by rw [hw, mul_sub f c p, hfc, hfp]
        _ = k₁ - k₂ := by simp

end GlobalTheory.CompanionTheory.NullFr.Packing
