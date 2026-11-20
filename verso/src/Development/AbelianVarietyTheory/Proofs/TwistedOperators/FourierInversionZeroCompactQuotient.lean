import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompactQuotientFourier

/- English proof (translation)
Establish `h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ` using `h𝓕.vadd_of_comm u`. Rewrite using `[h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]`. Establish `h2` using `(measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕`. Simplify using `only [add_comm _ u]`. Conclude with `h2.symm`.
-/
theorem setIntegral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ _ χ hc hx ha hn hker hinj μ 𝓕 hμ h𝓕 h1 Φ hΦ hper hsum`. Use `haveI := hμ`. Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `: IsFiniteMeasure (μ.restrict 𝓕)` using `⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Establish `hvol : μ.real 𝓕 = 1` using `by simp [Measure.real, h1]`.

Establish `hne : ∀ a x, χ a x ≠ 0` using `fun a x h => by simpa [h] using hn a x`. Establish `hχ0 : ∀ x, χ 0 x = 1` using `fun x => by`. Establish `h2 : χ 0 x * χ 0 x = χ 0 x * 1` using `by rw [mul_one, ← ha, add_zero]`. Conclude with `mul_left_cancel₀ (hne 0 x) h2`. Establish `hχx0 : ∀ a, χ a 0 = 1` using `fun a => by`.

Establish `h2 : χ a 0 * χ a 0 = χ a 0 * 1` using `by rw [mul_one, ← hx, add_zero]`. Conclude with `mul_left_cancel₀ (hne a 0) h2`. Establish `hstar : ∀ a x, star (χ a x) = χ (-a) x` using `fun a x => by`. Establish `h1' : χ (-a) x * χ a x = 1` using `by rw [← ha, neg_add_cancel, hχ0]`. Establish `h2 : star (χ a x) * χ a x = 1` using `by simp [Complex.conj_mul', hn]`.

Conclude with `mul_right_cancel₀ (hne a x) (h2.trans h1'.symm)`. Establish `hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x` using `fun a γ hγ x => by`. Rewrite using `[hx, (hker γ).2 hγ a, one_mul]`. Establish `horth : ∀ a b, ∫ x in 𝓕, χ b x * star (χ a x) ∂μ = if a = b then 1 else 0`. Introduce `a b`.

Establish `he : ∀ x, χ b x * star (χ a x) = χ (b - a) x` using `fun x => by rw [hstar, ← ha, sub_eq_add_neg]`. Repeatedly rewrite using `[he]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Simplify using `[hχ0, hvol]`.

Establish `hc' : b - a ≠ 0` using `sub_ne_zero.2 (Ne.symm hab)`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x₀, χ (b - a) x₀ ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc' (hinj _ h)`.

Establish `key` using `setIntegral_translate Γ μ 𝓕 h𝓕 (χ (b - a)) (hperχ _) x₀`. Rewrite `key` using `[hx _ _ x₀]`. Rewrite `key` using `[integral_mul_const]`. Establish `h3 : (∫ x in 𝓕, χ (b - a) x ∂μ) * (χ (b - a) x₀ - 1) = 0`. Rewrite using `[mul_sub, key, mul_one, sub_self]`.

Conclude with `(mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hx₀)`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hΦ.continuousOn`. Establish `hΦb : ∀ x, ‖Φ x‖ ≤ C` using `fun x => by`. Take `⟨γ, hγ, hk⟩` from `hcov x`. Rewrite using `[← hper γ hγ x]`.

Conclude with `hC _ hk`. Establish `hint : ∀ f : G → ℂ, Continuous f → ∀ B, (∀ x, ‖f x‖ ≤ B) → Integrable f (μ.restrict 𝓕)` using `fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)`. Use `set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef`. Establish `hterm : ∀ a x, ‖c a * star (χ a x)‖ = ‖c a‖` using `fun a x => by`. Rewrite using `[norm_mul, norm_star, hn, mul_one]`.

Set `S : G → ℂ` to `fun x => ∑' a, c a * star (χ a x)`. Establish `hScont : Continuous S` using `continuous_tsum (fun a => continuous_const.mul (hc a).star) hsum (fun a x => (hterm a x).le)`. Establish `hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x` using `fun γ hγ x => by`. Simplify using `only [S, hperχ _ γ hγ]`. Establish `hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖` using `fun x => by`.

Establish `hs : Summable (fun a => ‖c a * star (χ a x)‖)` using `by simp_rw [hterm]; exact hsum`. Combine the equalities or inequalities in the displayed calculation. Establish `hcS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b`. Introduce `b`. Establish `e : ∀ x, χ b x * S x = ∑' a, χ b x * (c a * star (χ a x))` using `fun x => tsum_mul_left.symm`.

Establish `hnorm : ∀ a x, ‖χ b x * (c a * star (χ a x))‖ = ‖c a‖` using `fun a x => by`. Rewrite using `[norm_mul, hn, one_mul, hterm]`. Establish `hFi : ∀ a, Integrable (fun x => χ b x * (c a * star (χ a x))) (μ.restrict 𝓕)` using `fun a => hint _ ((hc b).mul (continuous_const.mul (hc a).star)) ‖c a‖ fun x => (hnorm a x).le`. Establish `hFs : Summable fun a => ∫ x in 𝓕, ‖χ b x * (c a * star (χ a x))‖ ∂μ`. Repeatedly rewrite using `[hnorm]`.

Simplify `hsum` using `[hvol]`. Establish `e2 : ∀ a, ∫ x in 𝓕, χ b x * (c a * star (χ a x)) ∂μ = c a * (if a = b then 1 else 0)` using `fun a => by`. Rewrite using `[← horth, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[← integral_tsum_of_summable_integral_norm hFi hFs]`. Repeatedly rewrite using `[e2, mul_ite, mul_one, mul_zero]`. Simplify using the standard rewrite rules.

Establish `hdiff` using `GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha hχ0 hn hker μ 𝓕 hμ h𝓕 (Φ - S) (hΦ.sub hScont) (fun γ hγ x => by simp only [Pi.sub_apply, hper γ hγ, hSper γ hγ]) (fun a => by`. Simplify using `only [Pi.sub_apply, mul_sub]`. Establish `i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕)` using `hint _ ((hc a).mul hΦ) C fun x => by rw [norm_mul, hn, one_mul]; exact hΦb x`. Establish `i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕)` using `hint _ ((hc a).mul hScont) _ fun x => by rw [norm_mul, hn, one_mul]; exact hSb x`. Rewrite using `[integral_sub i1 i2, hcS, sub_self])`.

Establish `h0` using `congrFun hdiff 0`. Simplify using `only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h0`. Rewrite using `[h0]`. Simplify using `only [S, hχx0, star_one, mul_one]`.
-/
theorem inversion_at_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ _ χ hc hx ha hn hker hinj μ 𝓕 hμ h𝓕 h1 Φ hΦ hper hsum
  classical
  haveI := hμ
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hχ0 : ∀ x, χ 0 x = 1 := fun x => by
    have h2 : χ 0 x * χ 0 x = χ 0 x * 1 := by rw [mul_one, ← ha, add_zero]
    exact mul_left_cancel₀ (hne 0 x) h2
  have hχx0 : ∀ a, χ a 0 = 1 := fun a => by
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [mul_one, ← hx, add_zero]
    exact mul_left_cancel₀ (hne a 0) h2
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := fun a x => by
    have h1' : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, hχ0]
    have h2 : star (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
    exact mul_right_cancel₀ (hne a x) (h2.trans h1'.symm)
  have hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := fun a γ hγ x => by
    rw [hx, (hker γ).2 hγ a, one_mul]
  have horth : ∀ a b, ∫ x in 𝓕, χ b x * star (χ a x) ∂μ = if a = b then 1 else 0 := by
    intro a b
    have he : ∀ x, χ b x * star (χ a x) = χ (b - a) x := fun x => by rw [hstar, ← ha, sub_eq_add_neg]
    simp_rw [he]
    split_ifs with hab
    · subst hab
      simp [hχ0, hvol]
    · have hc' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, χ (b - a) x₀ ≠ 1 := by
        by_contra h
        push_neg at h
        exact hc' (hinj _ h)
      have key := setIntegral_translate Γ μ 𝓕 h𝓕 (χ (b - a)) (hperχ _) x₀
      simp_rw [hx _ _ x₀] at key
      rw [integral_mul_const] at key
      have h3 : (∫ x in 𝓕, χ (b - a) x ∂μ) * (χ (b - a) x₀ - 1) = 0 := by
        rw [mul_sub, key, mul_one, sub_self]
      exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hx₀)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hΦb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← hper γ hγ x]
    exact hC _ hk
  have hint : ∀ f : G → ℂ, Continuous f → ∀ B, (∀ x, ‖f x‖ ≤ B) → Integrable f (μ.restrict 𝓕) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef
  have hterm : ∀ a x, ‖c a * star (χ a x)‖ = ‖c a‖ := fun a x => by
    rw [norm_mul, norm_star, hn, mul_one]
  let S : G → ℂ := fun x => ∑' a, c a * star (χ a x)
  have hScont : Continuous S :=
    continuous_tsum (fun a => continuous_const.mul (hc a).star) hsum (fun a x => (hterm a x).le)
  have hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x := fun γ hγ x => by
    simp only [S, hperχ _ γ hγ]
  have hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖ := fun x => by
    have hs : Summable (fun a => ‖c a * star (χ a x)‖) := by simp_rw [hterm]; exact hsum
    calc ‖S x‖ ≤ ∑' a, ‖c a * star (χ a x)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' a, ‖c a‖ := by simp_rw [hterm]
  have hcS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b := by
    intro b
    have e : ∀ x, χ b x * S x = ∑' a, χ b x * (c a * star (χ a x)) := fun x => tsum_mul_left.symm
    have hnorm : ∀ a x, ‖χ b x * (c a * star (χ a x))‖ = ‖c a‖ := fun a x => by
      rw [norm_mul, hn, one_mul, hterm]
    have hFi : ∀ a, Integrable (fun x => χ b x * (c a * star (χ a x))) (μ.restrict 𝓕) := fun a =>
      hint _ ((hc b).mul (continuous_const.mul (hc a).star)) ‖c a‖ fun x => (hnorm a x).le
    have hFs : Summable fun a => ∫ x in 𝓕, ‖χ b x * (c a * star (χ a x))‖ ∂μ := by
      simp_rw [hnorm]
      simpa [hvol] using hsum
    have e2 : ∀ a, ∫ x in 𝓕, χ b x * (c a * star (χ a x)) ∂μ = c a * (if a = b then 1 else 0) := fun a => by
      rw [← horth, ← integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [e]
    rw [← integral_tsum_of_summable_integral_norm hFi hFs]
    simp_rw [e2, mul_ite, mul_one, mul_zero]
    simp
  have hdiff := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha hχ0 hn hker
    μ 𝓕 hμ h𝓕 (Φ - S) (hΦ.sub hScont) (fun γ hγ x => by simp only [Pi.sub_apply, hper γ hγ, hSper γ hγ])
    (fun a => by
      simp only [Pi.sub_apply, mul_sub]
      have i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hΦ) C fun x => by rw [norm_mul, hn, one_mul]; exact hΦb x
      have i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hScont) _ fun x => by rw [norm_mul, hn, one_mul]; exact hSb x
      rw [integral_sub i1 i2, hcS, sub_self])
  have h0 := congrFun hdiff 0
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  simp only [S, hχx0, star_one, mul_one]

end GlobalTheory.CompactQuotientFourier
