import Mathlib
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hunder : w''.under (𝓞 E) = w` using `HeightOneSpectrum.ext hw`. Establish `hc : ∀ c : E, w.valuation E c ≤ 1 → w''.valuation E' (algebraMap E E' c) ≤ 1`. Introduce `c hc`. Substitute `hunder` using the available equality. Establish `: w''.asIdeal.LiesOver (w''.under (𝓞 E)).asIdeal` using `⟨rfl⟩`.

Rewrite using `[← HeightOneSpectrum.valuation_liesOver E' (w''.under (𝓞 E)) w'' c]`. Conclude with `pow_le_one' hc _`. Establish `hb : ∀ i, w''.valuation E' (b i) ≤ 1`. Introduce `i`. Establish `: b i = algebraMap (𝓞 E') E' (⟨b i, (mem_integralClosure_iff ℤ E').2 (hbi i)⟩ : 𝓞 E')` using `rfl`.

Rewrite using `[this]`. Conclude with `w''.valuation_le_one _`. Establish `hu : w''.valuation E' (ε * ε - ε) ≤ 1`. Rewrite using `[← b.sum_repr (ε * ε - ε)]`. Use `(Valuation.map_sum_le _ fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `mul_le_one' (hc _ (hε i)) (hb i)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h2 : w''.valuation E' (ε * ε) ≤ w''.valuation E' ε`.

Establish `: ε * ε = ε + (ε * ε - ε)` using `by ring`. Rewrite using `[this]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le le_rfl (hu.trans h.le))`. Rewrite `h2` using `[map_mul]`. Establish `h0 : (0 : _) < w''.valuation E' ε` using `lt_trans zero_lt_one h`.

Use `mul_lt_mul_of_pos_left h h0` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `absurd h2 (not_le.2 this)`.
-/
theorem integral_of_sq_sub_integral (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (hbi : ∀ i, IsIntegral ℤ (b i))
    (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E'))
    (hw : w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal) (ε : E')
    (hε : ∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) : w''.valuation E' ε ≤ 1 := by
  have hunder : w''.under (𝓞 E) = w := HeightOneSpectrum.ext hw
  have hc : ∀ c : E, w.valuation E c ≤ 1 → w''.valuation E' (algebraMap E E' c) ≤ 1 := by
    intro c hc
    subst hunder
    have : w''.asIdeal.LiesOver (w''.under (𝓞 E)).asIdeal := ⟨rfl⟩
    rw [← HeightOneSpectrum.valuation_liesOver E' (w''.under (𝓞 E)) w'' c]
    exact pow_le_one' hc _
  have hb : ∀ i, w''.valuation E' (b i) ≤ 1 := by
    intro i
    have : b i = algebraMap (𝓞 E') E' (⟨b i, (mem_integralClosure_iff ℤ E').2 (hbi i)⟩ : 𝓞 E') := rfl
    rw [this]
    exact w''.valuation_le_one _
  have hu : w''.valuation E' (ε * ε - ε) ≤ 1 := by
    rw [← b.sum_repr (ε * ε - ε)]
    refine (Valuation.map_sum_le _ fun i _ => ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_one' (hc _ (hε i)) (hb i)
  by_contra h
  push_neg at h
  have h2 : w''.valuation E' (ε * ε) ≤ w''.valuation E' ε := by
    have : ε * ε = ε + (ε * ε - ε) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl (hu.trans h.le))
  rw [map_mul] at h2
  have h0 : (0 : _) < w''.valuation E' ε := lt_trans zero_lt_one h
  have := mul_lt_mul_of_pos_left h h0
  rw [mul_one] at this
  exact absurd h2 (not_le.2 this)

end GlobalTheory
