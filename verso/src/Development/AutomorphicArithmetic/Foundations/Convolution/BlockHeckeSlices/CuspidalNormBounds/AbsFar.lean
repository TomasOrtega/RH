import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AbsGrow

open NumberField

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hm : (1 : ℝ) ≤ s.card` using `by exact_mod_cast Finset.card_pos.mpr ⟨p, hp⟩`. Establish `h1 : ‖∑ q ∈ s, (Λ p - Λ q)‖ ≤ s.card * D`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Use `Finset.sum_le_card_nsmul s (fun q => ‖Λ p - Λ q‖) D hne` as an intermediate fact. Simplify `this` using `[nsmul_eq_mul]`. Establish `h2 : (s.card : ℂ) * Λ p = ∑ q ∈ s, (Λ p - Λ q) + ∑ q ∈ s, Λ q`. Simplify using `[Finset.sum_sub_distrib, nsmul_eq_mul]`. Establish `h3 : (s.card : ℝ) * ‖Λ p‖ ≤ s.card * D + S₀`.

Establish `: ‖(s.card : ℂ) * Λ p‖ = (s.card : ℝ) * ‖Λ p‖` using `by simp`. Rewrite using `[← this, h2]`. Conclude with `(norm_add_le _ _).trans (add_le_add h1 hS)`. Establish `h4` using `le_abs_self S₀`. Establish `h5` using `abs_nonneg S₀`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem exists_far {ι : Type} (s : Finset ι) (Λ : ι → ℂ) (p : ι) (hp : p ∈ s) (S₀ D : ℝ)
    (hS : ‖∑ q ∈ s, Λ q‖ ≤ S₀) (hB : D + |S₀| < ‖Λ p‖) : ∃ q ∈ s, D < ‖Λ p - Λ q‖ := by
  by_contra hne
  push Not at hne
  have hm : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr ⟨p, hp⟩
  have h1 : ‖∑ q ∈ s, (Λ p - Λ q)‖ ≤ s.card * D := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul s (fun q => ‖Λ p - Λ q‖) D hne
    simpa [nsmul_eq_mul] using this
  have h2 : (s.card : ℂ) * Λ p = ∑ q ∈ s, (Λ p - Λ q) + ∑ q ∈ s, Λ q := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  have h3 : (s.card : ℝ) * ‖Λ p‖ ≤ s.card * D + S₀ := by
    have : ‖(s.card : ℂ) * Λ p‖ = (s.card : ℝ) * ‖Λ p‖ := by simp
    rw [← this, h2]
    exact (norm_add_le _ _).trans (add_le_add h1 hS)
  have h4 := le_abs_self S₀
  have h5 := abs_nonneg S₀
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hy' : 0 < y` using `lt_of_le_of_ne hy (Ne.symm hne)`. Establish `h1 : 1 < a / b` using `(one_lt_div hb).mpr hab`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (B / y) h1`. Rewrite `hk` using `[div_pow, div_lt_div_iff₀ hy' (pow_pos hb k)]`.

Combine the linear relations using `[h k]`.
-/
private theorem eq_zero_of_pow_le {a b y B : ℝ} (hb : 0 < b) (hab : b < a) (hy : 0 ≤ y)
    (h : ∀ k : ℕ, a ^ k * y ≤ B * b ^ k) : y = 0 := by
  by_contra hne
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
  have h1 : 1 < a / b := (one_lt_div hb).mpr hab
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B / y) h1
  rw [div_pow, div_lt_div_iff₀ hy' (pow_pos hb k)] at hk
  linarith [h k]

/- English proof (translation)
Introduce `τ _ _ n C S₀`. Take `⟨K, hK1, hK⟩` from `UpperTheory.ConvolutionTheory.FX.abs_growth τ n C`. Use `⟨2 * K + |S₀|, ?_⟩` and prove the remaining obligations. Introduce `κ A V r _ _ _ _ _ _ Z H I t c idx Λ h good hs hS ⟨p, hp⟩`. Take `⟨q, hq, hpq⟩` from `exists_far _ Λ p (by simp) S₀ (2 * K) (hS (idx p.2)) hp`.

Establish `hidx : idx q.2 = idx p.2` using `(Finset.mem_filter.mp hq).2`. Use extensionality with `φ x`. Take `⟨B, hB⟩` from `hK κ A V r Z H I t c idx Λ h good hs φ ‖x‖`. Use `set X : τ × Fin n → A := fun q => algebraMap ℂ A (Λ q) + I (idx q.2) with hX`. Establish `hmon : ∀ a b : ℕ, ‖c ((X p ^ a * X q ^ b) • φ) x‖ ≤ B * K ^ (a + b)`.

Introduce `a b`. Use `hB (Finsupp.single p a + Finsupp.single q b) x le_rfl` as an intermediate fact. Rewrite `this` using `[MvPolynomial.monomial_add_single, ← MvPolynomial.X_pow_eq_monomial]`. Simplify using `using this`. Establish `hδ : X p - X q = algebraMap ℂ A (Λ p - Λ q)`.

Simplify using `only [hX, hidx, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ k : ℕ, ‖Λ p - Λ q‖ ^ k * ‖c φ x‖ ≤ B * (2 * K) ^ k`. Introduce `k`. Establish `e1 : c ((X p - X q) ^ k • φ) x = (Λ p - Λ q) ^ k * c φ x`.

Rewrite using `[hδ, ← map_pow, algebraMap_smul, map_smul]`. Both sides reduce to the same expression. Establish `e2 : (X p - X q) ^ k • φ = ∑ m ∈ Finset.range (k + 1), (((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) • ((X p ^ m * X q ^ (k - m)) • φ))`. Rewrite using `[sub_pow, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul A ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)), smul_smul]`. Use `congr 1`. Simplify using `only [map_mul, map_pow, map_neg, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← norm_pow, ← norm_mul, ← e1, e2, map_sum, Finset.sum_apply]`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `e3 : B * (2 * K) ^ k = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (B * K ^ k)`. Rewrite using `[← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e3]`. Use `Finset.sum_le_sum fun m hm => ?_` and prove the remaining obligations. Establish `hmk : m + (k - m) = k` using `Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))`. Use `hmon m (k - m)` as an intermediate fact. Rewrite `this` using `[hmk]`.

Rewrite using `[map_smul, Pi.smul_apply, norm_smul]`. Simplify using `only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)`. Use `eq_zero_of_pow_le (by linarith) hpq (norm_nonneg _) key` as an intermediate fact. Simplify using `using this`.
-/
theorem UpperTheory.ConvolutionTheory.BW.absFar :
    UpperTheory.ConvolutionTheory.BW.AbsFar := by
  classical
  intro τ _ _ n C S₀
  obtain ⟨K, hK1, hK⟩ := UpperTheory.ConvolutionTheory.FX.abs_growth τ n C
  refine ⟨2 * K + |S₀|, ?_⟩
  intro κ A V r _ _ _ _ _ _ Z H I t c idx Λ h good hs hS ⟨p, hp⟩
  obtain ⟨q, hq, hpq⟩ := exists_far _ Λ p (by simp) S₀ (2 * K) (hS (idx p.2)) hp
  have hidx : idx q.2 = idx p.2 := (Finset.mem_filter.mp hq).2
  ext φ x
  obtain ⟨B, hB⟩ := hK κ A V r Z H I t c idx Λ h good hs φ ‖x‖
  set X : τ × Fin n → A := fun q => algebraMap ℂ A (Λ q) + I (idx q.2) with hX
  have hmon : ∀ a b : ℕ, ‖c ((X p ^ a * X q ^ b) • φ) x‖ ≤ B * K ^ (a + b) := by
    intro a b
    have := hB (Finsupp.single p a + Finsupp.single q b) x le_rfl
    rw [MvPolynomial.monomial_add_single, ← MvPolynomial.X_pow_eq_monomial] at this
    simpa using this
  have hδ : X p - X q = algebraMap ℂ A (Λ p - Λ q) := by
    simp only [hX, hidx, map_sub]; ring
  have key : ∀ k : ℕ, ‖Λ p - Λ q‖ ^ k * ‖c φ x‖ ≤ B * (2 * K) ^ k := by
    intro k
    have e1 : c ((X p - X q) ^ k • φ) x = (Λ p - Λ q) ^ k * c φ x := by
      rw [hδ, ← map_pow, algebraMap_smul, map_smul]; rfl
    have e2 : (X p - X q) ^ k • φ = ∑ m ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) • ((X p ^ m * X q ^ (k - m)) • φ)) := by
      rw [sub_pow, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← algebraMap_smul A ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)), smul_smul]
      congr 1
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
    rw [← norm_pow, ← norm_mul, ← e1, e2, map_sum, Finset.sum_apply]
    refine (norm_sum_le _ _).trans ?_
    have e3 : B * (2 * K) ^ k = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (B * K ^ k) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast; ring
    rw [e3]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmk : m + (k - m) = k := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    have := hmon m (k - m)
    rw [hmk] at this
    rw [map_smul, Pi.smul_apply, norm_smul]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have := eq_zero_of_pow_le (by linarith) hpq (norm_nonneg _) key
  simpa using this
