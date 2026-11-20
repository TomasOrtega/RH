import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate

open MeasureTheory Complex
open scoped Pointwise

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `hv : IsAddFundamentalDomain L (v +ᵥ D) volume` using `hD.vadd_of_comm v`. Establish `h1 : ∫ s in D, f (v + s) = ∫ s in v +ᵥ D, f s`. Use `(measurePreserving_add_left (volume : Measure (ι → ℝ)) v).setIntegral_image_emb (measurableEmbedding_addLeft v) f D` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Conclude with `hv.setIntegral_eq hD (fun p s => hf p.1 p.2 s)`.
-/
theorem fd_translate (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (f : (ι → ℝ) → ℂ) (hf : ∀ p ∈ L, ∀ s, f (p + s) = f s)
    (v : ι → ℝ) : ∫ s in D, f (v + s) = ∫ s in D, f s := by
  have hv : IsAddFundamentalDomain L (v +ᵥ D) volume := hD.vadd_of_comm v
  have h1 : ∫ s in D, f (v + s) = ∫ s in v +ᵥ D, f s := by
    have := (measurePreserving_add_left (volume : Measure (ι → ℝ)) v).setIntegral_image_emb
      (measurableEmbedding_addLeft v) f D
    rw [← this]
    rfl
  rw [h1]
  exact hv.setIntegral_eq hD (fun p s => hf p.1 p.2 s)

/- English proof (translation)
Use `split_ifs with h0`. Substitute `h0` using the available equality. Simplify using `[Measure.real]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `h0 (funext h)`. Use `set e : (ι → ℝ) → ℂ := fun s => cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) with he`. Establish `hadd : ∀ v s : ι → ℝ, e (v + s) = cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) * e s`. Introduce `v s`.

Simplify using `only [he, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]`. Establish `hinv : ∀ p ∈ L, ∀ s, e (p + s) = e s`. Introduce `p hp s`. Take `⟨k, hk⟩` from `hμ p hp`. Rewrite using `[hadd]`.

Establish `hk' : (2 : ℂ) * ∑ i, (μ i : ℂ) * (p i : ℂ) = k` using `by exact_mod_cast hk`. Establish `h2 : 4 * (Real.pi : ℂ) * I * ∑ i, (μ i : ℂ) * (p i : ℂ) = k * (2 * Real.pi * I)`. Take the linear combination `(2 * (Real.pi : ℂ) * I) * hk'`. Rewrite using `[h2, Complex.exp_int_mul_two_pi_mul_I, one_mul]`. Set `v : ι → ℝ` to `Pi.single j (1 / (4 * μ j))`.

Establish `hsumR : ∑ i, μ i * v i = 1 / 4`. Rewrite using `[Finset.sum_eq_single j (fun i _ hi => by simp [v, Pi.single_apply, hi]) (by simp)]`. Simplify using `only [v, Pi.single_eq_same]`. Clear the denominators using the available nonvanishing facts. Establish `hsum : ∑ i, (μ i : ℂ) * (v i : ℂ) = 1 / 4`.

Establish `h` using `congrArg Complex.ofReal hsumR`. Move the coercions through the operations in `at h`. Conclude with `h`. Establish `hexp : cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) = -1`. Rewrite using `[hsum]`.

Establish `h3 : 4 * (Real.pi : ℂ) * I * (1 / 4) = Real.pi * I` using `by ring`. Rewrite using `[h3, Complex.exp_pi_mul_I]`. Establish `htr` using `fd_translate L D hD e hinv v`. Simplify using `only [hadd, hexp, neg_one_mul, integral_neg] at htr`. Take the linear combination `(-1 / 2 : ℂ) * htr`.
-/
theorem orth (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (μ : ι → ℝ) (hμ : ∀ p ∈ L, ∃ k : ℤ, 2 * ∑ i, μ i * p i = k) :
    ∫ s in D, cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) =
      if μ = 0 then ((volume D).toReal : ℂ) else 0 := by
  split_ifs with h0
  · subst h0
    simp [Measure.real]
  · obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (funext h)
    classical
    set e : (ι → ℝ) → ℂ := fun s => cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) with he
    have hadd : ∀ v s : ι → ℝ,
        e (v + s) = cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) * e s := by
      intro v s
      simp only [he, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib,
        Complex.exp_add]
    have hinv : ∀ p ∈ L, ∀ s, e (p + s) = e s := by
      intro p hp s
      obtain ⟨k, hk⟩ := hμ p hp
      rw [hadd]
      have hk' : (2 : ℂ) * ∑ i, (μ i : ℂ) * (p i : ℂ) = k := by exact_mod_cast hk
      have h2 : 4 * (Real.pi : ℂ) * I * ∑ i, (μ i : ℂ) * (p i : ℂ) = k * (2 * Real.pi * I) := by
        linear_combination (2 * (Real.pi : ℂ) * I) * hk'
      rw [h2, Complex.exp_int_mul_two_pi_mul_I, one_mul]

    let v : ι → ℝ := Pi.single j (1 / (4 * μ j))
    have hsumR : ∑ i, μ i * v i = 1 / 4 := by
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [v, Pi.single_apply, hi]) (by simp)]
      simp only [v, Pi.single_eq_same]
      field_simp
    have hsum : ∑ i, (μ i : ℂ) * (v i : ℂ) = 1 / 4 := by
      have h := congrArg Complex.ofReal hsumR
      push_cast at h
      exact h
    have hexp : cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) = -1 := by
      rw [hsum]
      have h3 : 4 * (Real.pi : ℂ) * I * (1 / 4) = Real.pi * I := by ring
      rw [h3, Complex.exp_pi_mul_I]
    have htr := fd_translate L D hD e hinv v
    simp only [hadd, hexp, neg_one_mul, integral_neg] at htr
    linear_combination (-1 / 2 : ℂ) * htr

end ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
