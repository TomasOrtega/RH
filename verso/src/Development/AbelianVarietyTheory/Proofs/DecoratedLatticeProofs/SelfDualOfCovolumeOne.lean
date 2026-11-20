import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient

open MeasureTheory Topology

namespace GlobalTheory.CovolumeOneSelfDual

/- English proof (translation)
Establish `hm : ∀ γ : Γ, AEStronglyMeasurable (fun y => c (γ + y)) (μ.restrict 𝓕)`. Introduce `γ`. Use `hc.1.comp_quasiMeasurePreserving (measurePreserving_add_left μ (γ : G)).quasiMeasurePreserving` as an intermediate fact. Conclude with `this.restrict`. Establish `hl : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ`.

Rewrite using `[hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]`. Both sides reduce to the same expression. Establish `hfin : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤`. Rewrite using `[hl]`. Conclude with `hc.2.ne`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ∫⁻ y in 𝓕, ∑' γ : Γ, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤`. Rewrite using `[lintegral_tsum fun γ => (hm γ).enorm]`. Conclude with `hfin`. Establish `h2 : AEMeasurable (fun y => ∑' γ : Γ, ‖c (γ + y)‖ₑ) (μ.restrict 𝓕)` using `AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm`.

Use `filter_upwards [ae_lt_top' h2 h1] with y hy`. Establish `: ∑' γ : Γ, (‖c (γ + y)‖₊ : ENNReal) ≠ ⊤`. Simplify `hy.ne` using `only [enorm_eq_nnnorm]`. Conclude with `(NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl`. Rewrite using `[integral_tsum hm hfin, hF.integral_eq_tsum'' c hc]`.

Both sides reduce to the same expression.
-/
theorem unfold {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (hF : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : Γ => ‖c (γ + y)‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' γ : Γ, c (γ + y) ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun y => c (γ + y)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_left μ (γ : G)).quasiMeasurePreserving
    exact this.restrict
  have hl : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    rfl
  have hfin : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne
  refine ⟨?_, ?_⟩
  · have h1 : ∫⁻ y in 𝓕, ∑' γ : Γ, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : Γ, ‖c (γ + y)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : Γ, (‖c (γ + y)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  · rw [integral_tsum hm hfin, hF.integral_eq_tsum'' c hc]
    rfl

/- English proof (translation)
Establish `hK` using `(hs.isCompact.prod hC).image (f := fun p : G × G => p.1 - p.2) (by fun_prop)`. Establish `ht : Filter.Tendsto ((↑) : Γ → G) Filter.cofinite (Filter.cocompact G)` using `AddSubgroup.tendsto_coe_cofinite_of_discrete Γ (isDiscrete_iff_discreteTopology.2 inferInstance)`. Establish `hfin` using `ht hK.compl_mem_cocompact`. Rewrite `hfin` using `[Filter.mem_map, Filter.mem_cofinite]`. Use `hfin.subset ?_` and prove the remaining obligations.

Introduce and unpack `γ ⟨x, hx, h⟩ hn`. Conclude with `hn ⟨(γ + x, x), ⟨subset_tsupport f h, hx⟩, by simp⟩`.
-/
theorem finite_contributing {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hs : HasCompactSupport f)
    {C : Set G} (hC : IsCompact C) : {γ : Γ | ∃ x ∈ C, f (γ + x) ≠ 0}.Finite := by
  have hK := (hs.isCompact.prod hC).image (f := fun p : G × G => p.1 - p.2) (by fun_prop)
  have ht : Filter.Tendsto ((↑) : Γ → G) Filter.cofinite (Filter.cocompact G) :=
    AddSubgroup.tendsto_coe_cofinite_of_discrete Γ (isDiscrete_iff_discreteTopology.2 inferInstance)
  have hfin := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro γ ⟨x, hx, h⟩ hn
  exact hn ⟨(γ + x, x), ⟨subset_tsupport f h, hx⟩, by simp⟩

/- English proof (translation)
Establish `hlf : LocallyFinite fun γ : Γ => Function.support fun x : G => f (γ + x)`. Introduce `x`. Take `⟨C, hC, hx⟩` from `exists_compact_mem_nhds x`. Use `⟨C, hx, (finite_contributing Γ hs hC).subset ?_⟩` and prove the remaining obligations. Introduce and unpack `γ ⟨p, h, h1⟩`.

Conclude with `⟨p, h1, h⟩`. Establish `h : Continuous fun x : G => ∑ᶠ γ : Γ, f (γ + x)` using `continuous_finsum (fun γ => by fun_prop) hlf`. Use `h.congr fun x => (tsum_eq_finsum ?_).symm` and prove the remaining obligations. Use `(finite_contributing Γ hs (isCompact_singleton (x := x))).subset ?_` and prove the remaining obligations. Introduce `γ hγ`.

Conclude with `⟨x, rfl, hγ⟩`.
-/
theorem continuous_periodization {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) : Continuous fun x : G => ∑' γ : Γ, f (γ + x) := by
  have hlf : LocallyFinite fun γ : Γ => Function.support fun x : G => f (γ + x) := by
    intro x
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    refine ⟨C, hx, (finite_contributing Γ hs hC).subset ?_⟩
    rintro γ ⟨p, h, h1⟩
    exact ⟨p, h1, h⟩
  have h : Continuous fun x : G => ∑ᶠ γ : Γ, f (γ + x) :=
    continuous_finsum (fun γ => by fun_prop) hlf
  refine h.congr fun x => (tsum_eq_finsum ?_).symm
  refine (finite_contributing Γ hs (isCompact_singleton (x := x))).subset ?_
  intro γ hγ
  exact ⟨x, rfl, hγ⟩

section

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : G → G → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure G) (𝓕 : Set G) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)

include hK hcov hc hsy hadd hn hker hinj hμ hF h1

/- English proof (translation)
Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hc' : ∀ y, Continuous (B y)` using `fun y => (hc y).congr fun x => hsy x y`. Establish `hadd' : ∀ y x x', B y (x + x') = B y x * B y x'` using `fun y x x' => by`. Rewrite using `[hsy y, hadd, hsy x, hsy x']`. Establish `hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ`.

Introduce `γ`. Establish `hi : Integrable (fun x => f x * B x γ) μ` using `(hf.mul (hc γ)).integrable_of_hasCompactSupport hs.mul_right`. Rewrite using `[(unfold Γ μ 𝓕 hF _ hi).2]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]`. Establish `key` using `GlobalTheory.CompactQuotientFourier.inversion_at_zero G Γ K hK hcov Γ (fun γ x => B γ x) (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x) (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩) (fun a h => Subtype. …`. Rewrite using `[← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]`.

Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Simplify using `[add_assoc])`. Use the proof step `(by simp only [hcoef]; exact hsum)`. Simplify using `only [hcoef, add_zero] at key`. Conclude with `key`.
-/
theorem poisson {f : G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hsum : Summable fun γ : Γ => ‖∫ x, f x * B x γ ∂μ‖) :
    ∑' ξ : Γ, f ξ = ∑' γ : Γ, ∫ x, f x * B x γ ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  have hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ := by
    intro γ
    have hi : Integrable (fun x => f x * B x γ) μ :=
      (hf.mul (hc γ)).integrable_of_hasCompactSupport hs.mul_right
    rw [(unfold Γ μ 𝓕 hF _ hi).2]
    congr 1
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]
  have key := GlobalTheory.CompactQuotientFourier.inversion_at_zero G Γ K hK hcov Γ (fun γ x => B γ x)
    (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x)
    (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    (fun a h => Subtype.ext (hinj a a.2 h)) μ 𝓕 hμ hF h1 (fun x => ∑' ξ : Γ, f (ξ + x))
    (continuous_periodization Γ hf hs)
    (fun γ hγ x => by
      rw [← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]
      refine tsum_congr fun ξ => ?_
      simp [add_assoc])
    (by simp only [hcoef]; exact hsum)
  simp only [hcoef, add_zero] at key
  exact key

/- English proof (translation)
Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `: IsFiniteMeasure (μ.restrict 𝓕)` using `⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Establish `hvol : μ.real 𝓕 = 1` using `by simp [Measure.real, h1]`. Establish `hc' : ∀ y, Continuous (B y)` using `fun y => (hc y).congr fun x => hsy x y`. Establish `hadd' : ∀ y x x', B y (x + x') = B y x * B y x'` using `fun y x x' => by`.

Rewrite using `[hsy y, hadd, hsy x, hsy x']`. Take `⟨hae, hint⟩` from `unfold Γ μ 𝓕 hF _ hI`. Establish `he : ∀ (y : G) (γ : Γ), ∫ x, Φ x * B x (γ + y) ∂μ = ∫ x, (Φ x * B x y) * B x γ ∂μ`. Introduce `y γ`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[hadd']`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∫ y in 𝓕, ∑' γ : Γ, (∫ x, Φ x * B x (γ + y) ∂μ) ∂μ = ∫ y in 𝓕, ∑' ξ : Γ, Φ ξ * B ξ y ∂μ`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with y hy`. Simplify using `only [he] at hy ⊢`. Conclude with `(poisson Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1 (hΦ.mul (hc y)) hs.mul_right hy).symm`. Establish `hfin : {ξ : Γ | Φ ξ ≠ 0}.Finite`. Use `(finite_contributing Γ hs (isCompact_singleton (x := (0 : G)))).subset ?_` and prove the remaining obligations.

Introduce `ξ hξ`. Conclude with `⟨0, rfl, by simpa using hξ⟩`. Establish `hFi : ∀ ξ : Γ, Integrable (fun y => Φ ξ * B ξ y) (μ.restrict 𝓕)` using `fun ξ => Integrable.of_bound (continuous_const.mul (hc' ξ)).aestronglyMeasurable ‖Φ ξ‖ (Filter.Eventually.of_forall fun y => by rw [norm_mul, hn, mul_one])`. Establish `hFs : Summable fun ξ : Γ => ∫ y in 𝓕, ‖Φ ξ * B ξ y‖ ∂μ`. Use `summable_of_finite_support (hfin.subset ?_)` and prove the remaining obligations.

Introduce `ξ hξ h0`. Conclude with `hξ (by simp [h0])`. Establish `horth : ∀ ξ : Γ, ξ ≠ 0 → ∫ y in 𝓕, B ξ y ∂μ = 0`. Introduce `ξ hξ`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, B ξ u ≠ 1 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hξ (Subtype.ext (hinj ξ ξ.2 h))`. Establish `key` using `GlobalTheory.CompactQuotientFourier.setIntegral_translate Γ μ 𝓕 hF (B ξ) (fun γ hγ w => by rw [hadd', (hker γ).2 hγ ξ ξ.2, one_mul]) u`. Rewrite `key` using `[hadd' _ _ u]`.

Rewrite `key` using `[integral_mul_const]`. Establish `h3 : (∫ y in 𝓕, B ξ y ∂μ) * (B ξ u - 1) = 0`. Rewrite using `[mul_sub, key, mul_one, sub_self]`. Conclude with `(mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hu)`. Establish `hB0 : ∀ y, B 0 y = 1` using `fun y => by`.

Rewrite using `[hsy]`. Establish `hne : B y 0 ≠ 0` using `fun h => by simpa [h] using hn y 0`. Establish `h2 : B y 0 * B y 0 = B y 0 * 1` using `by rw [mul_one, ← hadd', add_zero]`. Conclude with `mul_left_cancel₀ hne h2`. Rewrite using `[hint, h2, ← integral_tsum_of_summable_integral_norm hFi hFs, tsum_eq_single (0 : Γ)]`.

Simplify using `[hB0, hvol]`. Introduce `ξ hξ`. Rewrite using `[integral_const_mul, horth ξ hξ, mul_zero]`.
-/
theorem inversion_zero {Φ : G → ℂ} (hΦ : Continuous Φ) (hs : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * B x y ∂μ) μ) :
    ∫ y, (∫ x, Φ x * B x y ∂μ) ∂μ = Φ 0 := by
  classical
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  obtain ⟨hae, hint⟩ := unfold Γ μ 𝓕 hF _ hI
  have he : ∀ (y : G) (γ : Γ), ∫ x, Φ x * B x (γ + y) ∂μ = ∫ x, (Φ x * B x y) * B x γ ∂μ := by
    intro y γ
    congr 1
    funext x
    rw [hadd']
    ring
  have h2 : ∫ y in 𝓕, ∑' γ : Γ, (∫ x, Φ x * B x (γ + y) ∂μ) ∂μ = ∫ y in 𝓕, ∑' ξ : Γ, Φ ξ * B ξ y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [he] at hy ⊢
    exact (poisson Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1 (hΦ.mul (hc y)) hs.mul_right hy).symm
  have hfin : {ξ : Γ | Φ ξ ≠ 0}.Finite := by
    refine (finite_contributing Γ hs (isCompact_singleton (x := (0 : G)))).subset ?_
    intro ξ hξ
    exact ⟨0, rfl, by simpa using hξ⟩
  have hFi : ∀ ξ : Γ, Integrable (fun y => Φ ξ * B ξ y) (μ.restrict 𝓕) := fun ξ =>
    Integrable.of_bound (continuous_const.mul (hc' ξ)).aestronglyMeasurable ‖Φ ξ‖
      (Filter.Eventually.of_forall fun y => by rw [norm_mul, hn, mul_one])
  have hFs : Summable fun ξ : Γ => ∫ y in 𝓕, ‖Φ ξ * B ξ y‖ ∂μ := by
    refine summable_of_finite_support (hfin.subset ?_)
    intro ξ hξ h0
    exact hξ (by simp [h0])
  have horth : ∀ ξ : Γ, ξ ≠ 0 → ∫ y in 𝓕, B ξ y ∂μ = 0 := by
    intro ξ hξ
    obtain ⟨u, hu⟩ : ∃ u, B ξ u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (Subtype.ext (hinj ξ ξ.2 h))
    have key := GlobalTheory.CompactQuotientFourier.setIntegral_translate Γ μ 𝓕 hF (B ξ)
      (fun γ hγ w => by rw [hadd', (hker γ).2 hγ ξ ξ.2, one_mul]) u
    simp_rw [hadd' _ _ u] at key
    rw [integral_mul_const] at key
    have h3 : (∫ y in 𝓕, B ξ y ∂μ) * (B ξ u - 1) = 0 := by
      rw [mul_sub, key, mul_one, sub_self]
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hu)
  have hB0 : ∀ y, B 0 y = 1 := fun y => by
    rw [hsy]
    have hne : B y 0 ≠ 0 := fun h => by simpa [h] using hn y 0
    have h2 : B y 0 * B y 0 = B y 0 * 1 := by rw [mul_one, ← hadd', add_zero]
    exact mul_left_cancel₀ hne h2
  rw [hint, h2, ← integral_tsum_of_summable_integral_norm hFi hFs, tsum_eq_single (0 : Γ)]
  · simp [hB0, hvol]
  · intro ξ hξ
    rw [integral_const_mul, horth ξ hξ, mul_zero]

end

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hμ hF h1`. Use `⟨hμ, fun Φ hΦ hs hI z => ?_⟩` and prove the remaining obligations. Establish `he : ∀ y, ∫ x, Φ (x - z) * B x y ∂μ = (∫ x, Φ x * B x y ∂μ) * B y z`. Introduce `y`. Rewrite using `[← integral_add_right_eq_self (fun x => Φ (x - z) * B x y) z, ← integral_mul_const]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[add_sub_cancel_right, hadd, hsy z y, mul_assoc]`. Establish `hs' : HasCompactSupport fun x => Φ (x - z)` using `hs.comp_homeomorph (Homeomorph.subRight z)`. Establish `hI' : Integrable (fun y => ∫ x, Φ (x - z) * B x y ∂μ) μ`.

Simplify using `only [he]`. Conclude with `hI.mul_bdd (c := 1) (hc z).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y z).le)`. Establish `key` using `inversion_zero Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1 (Φ := fun x => Φ (x - z)) (by fun_prop) hs' hI'`. Simplify using `only [he, zero_sub] at key`. Conclude with `key`.
-/
theorem selfDual_of_covolume_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hμ hF h1
  refine ⟨hμ, fun Φ hΦ hs hI z => ?_⟩
  have he : ∀ y, ∫ x, Φ (x - z) * B x y ∂μ = (∫ x, Φ x * B x y ∂μ) * B y z := by
    intro y
    rw [← integral_add_right_eq_self (fun x => Φ (x - z) * B x y) z, ← integral_mul_const]
    congr 1
    funext x
    rw [add_sub_cancel_right, hadd, hsy z y, mul_assoc]
  have hs' : HasCompactSupport fun x => Φ (x - z) := hs.comp_homeomorph (Homeomorph.subRight z)
  have hI' : Integrable (fun y => ∫ x, Φ (x - z) * B x y ∂μ) μ := by
    simp only [he]
    exact hI.mul_bdd (c := 1) (hc z).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y z).le)
  have key := inversion_zero Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1
    (Φ := fun x => Φ (x - z)) (by fun_prop) hs' hI'
  simp only [he, zero_sub] at key
  exact key

end GlobalTheory.CovolumeOneSelfDual
