import Mathlib

open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.ClassIntegral

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

def dcoset (Γ K : Subgroup G) (g : G) : Set G := {x | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g * k}

/- English proof (translation)
Establish `: dcoset Γ K g = ⋃ γ : Γ, (fun y => ((γ : G) * g)⁻¹ * y) ⁻¹' (K : Set G)`. Use extensionality with `x`. Simplify using `only [dcoset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, k, hk, rfl⟩`.

Conclude with `⟨⟨γ, hγ⟩, by simpa [mul_assoc] using hk⟩`. Introduce and unpack `⟨γ, h⟩`. Conclude with `⟨γ, γ.2, _, h, by group⟩`. Rewrite using `[this]`. Conclude with `MeasurableSet.iUnion fun γ => (measurable_const_mul _) hK`.
-/
theorem measurableSet_dcoset (Γ K : Subgroup G) [Countable Γ] (hK : MeasurableSet (K : Set G)) (g : G) :
    MeasurableSet (dcoset Γ K g) := by
  have : dcoset Γ K g = ⋃ γ : Γ, (fun y => ((γ : G) * g)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext x
    simp only [dcoset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, by simpa [mul_assoc] using hk⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ, γ.2, _, h, by group⟩
  rw [this]
  exact MeasurableSet.iUnion fun γ => (measurable_const_mul _) hK

omit [MeasurableSpace G] [MeasurableMul G] in
/- English proof (translation)
Distinguish the cases in `hx : x ∈ dcoset Γ K g`. Rewrite using `[Set.indicator_of_mem hx, Pi.one_apply, mul_one]`. Take `⟨δ, hδ, k, hk, rfl⟩` from `hx`. Rewrite using `[← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)⁻¹).tsum_eq]`. Use `tsum_subtype {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} (fun _ => (1 : ENNReal))` as an intermediate fact.

Use `Eq.trans ?_ this.symm` and prove the remaining obligations. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Establish `e : g⁻¹ * ((γ : G) * δ⁻¹ * (δ * g * k)) = g⁻¹ * γ * g * k` using `by group`. Simplify using `only [Set.indicator, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe, Pi.one_apply, Set.mem_setOf_eq, e, K.mul_mem_cancel_right hk]`. Rewrite using `[Set.indicator_of_notMem hx, mul_zero, ENNReal.tsum_eq_zero]`.

Introduce `γ`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `h`. Apply `hx` to reduce the goal to its premises. Use `⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, h, ?_⟩` and prove the remaining obligations.

Simplify using `only [Subgroup.smul_def, smul_eq_mul]`. Use `group`.
-/
theorem tsum_indicator_eq (Γ K : Subgroup G) (g x : G) :
    ∑' γ : Γ, ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) =
      (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * (dcoset Γ K g).indicator 1 x := by
  classical
  by_cases hx : x ∈ dcoset Γ K g
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨δ, hδ, k, hk, rfl⟩ := hx
    rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)⁻¹).tsum_eq]
    have := tsum_subtype {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} (fun _ => (1 : ENNReal))
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun γ => ?_
    have e : g⁻¹ * ((γ : G) * δ⁻¹ * (δ * g * k)) = g⁻¹ * γ * g * k := by group
    simp only [Set.indicator, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Equiv.coe_mulRight,
      Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe, Pi.one_apply, Set.mem_setOf_eq, e,
      K.mul_mem_cancel_right hk]
  · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.tsum_eq_zero]
    intro γ
    apply Set.indicator_of_notMem
    intro h
    apply hx
    refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, h, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul]
    group

/- English proof (translation)
Establish `i1 : MeasurableConstSMul Γ G` using `⟨fun γ => by simpa [Subgroup.smul_def, smul_eq_mul] using measurable_const_mul (γ : G)⟩`. Establish `i2 : SMulInvariantMeasure Γ G μ` using `⟨fun γ s _ => by`. Establish `: ((fun x => γ • x) ⁻¹' s) = ((fun x => (γ : G) * x) ⁻¹' s)`. Use extensionality with `x`. Simplify using `[Subgroup.smul_def, smul_eq_mul]`.

Rewrite using `[this, measure_preimage_mul]⟩`. Establish `hT : MeasurableSet ((fun y => g⁻¹ * y) ⁻¹' (K : Set G))` using `(measurable_const_mul _) hK`. Establish `hf : Measurable (((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal))` using `measurable_one.indicator hT`. Establish `hC` using `measurableSet_dcoset Γ K hK g`. Rewrite using `[← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]`.

Simplify using `only [← tsum_indicator_eq]`. Establish `hmeas : ∀ γ : Γ, Measurable fun x : G => ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x)` using `fun γ => hf.comp (measurable_const_smul γ)`. Rewrite using `[lintegral_tsum fun γ => (hmeas γ).aemeasurable, ← h𝓕.lintegral_eq_tsum'', lintegral_indicator_one hT, measure_preimage_mul, hK1]`.
-/
theorem measure_dcoset (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) (g : G) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * μ.restrict 𝓕 (dcoset Γ K g) = 1 := by
  have i1 : MeasurableConstSMul Γ G :=
    ⟨fun γ => by simpa [Subgroup.smul_def, smul_eq_mul] using measurable_const_mul (γ : G)⟩
  have i2 : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => by
      have : ((fun x => γ • x) ⁻¹' s) = ((fun x => (γ : G) * x) ⁻¹' s) := by
        ext x; simp [Subgroup.smul_def, smul_eq_mul]
      rw [this, measure_preimage_mul]⟩
  have hT : MeasurableSet ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)) := (measurable_const_mul _) hK
  have hf : Measurable (((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)) :=
    measurable_one.indicator hT
  have hC := measurableSet_dcoset Γ K hK g
  rw [← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]
  simp only [← tsum_indicator_eq]
  have hmeas : ∀ γ : Γ, Measurable fun x : G =>
      ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) :=
    fun γ => hf.comp (measurable_const_smul γ)
  rw [lintegral_tsum fun γ => (hmeas γ).aemeasurable,
    ← h𝓕.lintegral_eq_tsum'', lintegral_indicator_one hT, measure_preimage_mul, hK1]

/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at h`. Establish `hN0 : (∑' _ : α, (1 : ENNReal)) ≠ 0` using `by intro h0; rw [h0] at h; simp at h`. Establish `hN : (∑' _ : α, (1 : ENNReal)) ≠ ⊤`. Introduce `h0`. Rewrite `h` using `[h0, ENNReal.top_mul hm0]`.

Simplify using `at h`. Establish `hm : m ≠ ⊤`. Introduce `h0`. Rewrite `h` using `[h0, ENNReal.mul_top hN0]`. Simplify using `at h`.

Establish `: Finite α`. Assume the negation of the conclusion as `hα`. Establish `: Infinite α` using `not_finite_iff_infinite.mp hα`. Conclude with `hN (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)`. Use `⟨hm, ?_⟩` and prove the remaining obligations.

Use `Fintype.ofFinite α` as an intermediate fact. Rewrite `h` using `[tsum_fintype]`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_eq_nat_card] at h`. Establish `h'` using `congrArg ENNReal.toReal h`. Rewrite `h'` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one]`.

Conclude with `eq_inv_of_mul_eq_one_right h'`.
-/
theorem tsum_one_mul_eq_one {α : Type} {m : ENNReal} (h : (∑' _ : α, (1 : ENNReal)) * m = 1) :
    m ≠ ⊤ ∧ m.toReal = (Nat.card α : ℝ)⁻¹ := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at h
  have hN0 : (∑' _ : α, (1 : ENNReal)) ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hN : (∑' _ : α, (1 : ENNReal)) ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.top_mul hm0] at h; simp at h
  have hm : m ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.mul_top hN0] at h; simp at h
  have : Finite α := by
    by_contra hα
    have : Infinite α := not_finite_iff_infinite.mp hα
    exact hN (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
  refine ⟨hm, ?_⟩
  have := Fintype.ofFinite α
  rw [tsum_fintype] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_eq_nat_card] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h'
  exact eq_inv_of_mul_eq_one_right h'

/- English proof (translation)
Introduce `G _ _ _ Γ K _ μ _ hK hK1 ι _ g hcov 𝓕 h𝓕 Φ hΦ`. Establish `hm` using `fun i => tsum_one_mul_eq_one (measure_dcoset Γ K μ hK hK1 (g i) h𝓕)`. Establish `hC` using `fun i => measurableSet_dcoset Γ K hK (g i)`. Establish `hpt : Φ = fun x => ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x`. Use function extensionality and compare the values at `x`.

Take `⟨j, hj, huniq⟩` from `hcov x`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Set.indicator_of_mem (s := dcoset Γ K (g j)) hj]`. Take `⟨γ, hγ, k, hk, rfl⟩` from `hj`. Conclude with `hΦ γ hγ k hk _`.

Introduce `i _ hij`. Establish `hx : x ∉ dcoset Γ K (g i)` using `fun h => hij (huniq i h)`. Conclude with `Set.indicator_of_notMem hx _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.

Establish `hint : ∀ i, Integrable ((dcoset Γ K (g i)).indicator (fun _ => Φ (g i))) (μ.restrict 𝓕)` using `fun i => (integrable_indicator_iff (hC i)).mpr (integrableOn_const (hm i).1)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[IntegrableOn, hpt]`. Conclude with `integrable_finset_sum _ fun i _ => hint i`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[integral_finset_sum _ fun i _ => hint i]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hC i), Measure.real, (hm i).2, Complex.real_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem integral_fundamentalDomain_eq_sum : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant], MeasurableSet (K : Set G) → μ K = 1 → ∀ {ι : Type} [Fintype ι] (g : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g i * k) → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, (∀ γ ∈ Γ, ∀ k ∈ K, ∀ x, Φ (γ * x * k) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∑ i, ((Nat.card {γ : Γ // (g i)⁻¹ * (γ : G) * g i ∈ K} : ℂ))⁻¹ * Φ (g i) := by
  intro G _ _ _ Γ K _ μ _ hK hK1 ι _ g hcov 𝓕 h𝓕 Φ hΦ
  have hm := fun i => tsum_one_mul_eq_one (measure_dcoset Γ K μ hK hK1 (g i) h𝓕)
  have hC := fun i => measurableSet_dcoset Γ K hK (g i)
  have hpt : Φ = fun x => ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x := by
    funext x
    obtain ⟨j, hj, huniq⟩ := hcov x
    rw [Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem (s := dcoset Γ K (g j)) hj]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hj
      exact hΦ γ hγ k hk _
    · intro i _ hij
      have hx : x ∉ dcoset Γ K (g i) := fun h => hij (huniq i h)
      exact Set.indicator_of_notMem hx _
    · intro h; exact absurd (Finset.mem_univ j) h
  have hint : ∀ i, Integrable ((dcoset Γ K (g i)).indicator (fun _ => Φ (g i))) (μ.restrict 𝓕) :=
    fun i => (integrable_indicator_iff (hC i)).mpr (integrableOn_const (hm i).1)
  constructor
  · rw [IntegrableOn, hpt]
    exact integrable_finset_sum _ fun i _ => hint i
  · calc ∫ x in 𝓕, Φ x ∂μ
        = ∫ x in 𝓕, ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x ∂μ := by
          conv_lhs => rw [hpt]
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => hint i]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_indicator_const _ (hC i), Measure.real, (hm i).2, Complex.real_smul]
          push_cast
          rfl

end GlobalTheory.ClassIntegral
