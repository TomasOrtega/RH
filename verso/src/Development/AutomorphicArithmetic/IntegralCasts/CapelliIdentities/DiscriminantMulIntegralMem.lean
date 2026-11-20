import Mathlib

/- English proof (translation)
Establish `h1 : IsIntegral ℤ r`. Establish `h2 : IsIntegral ℤ (algebraMap ℚ K r)` using `by simpa using h`. Conclude with `(isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h2`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h1`. Conclude with `⟨a, by simpa using ha⟩`.
-/
private theorem int_of_rat {K : Type} [Field K] [CharZero K] (r : ℚ)
    (h : IsIntegral ℤ (r : K)) : ∃ a : ℤ, (a : ℚ) = r := by
  have h1 : IsIntegral ℤ r := by
    have h2 : IsIntegral ℤ (algebraMap ℚ K r) := by simpa using h
    exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨a, by simpa using ha⟩

/- English proof (translation)
Introduce `K _ _ σ w y t n ht hn hy hmem`. Establish `hsq : w * w = (t : K) * w - (n : K)` using `by linear_combination w * ht - hn`. Establish `hw : IsIntegral ℤ w`. Use `⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`.

Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X, eq_intCast, eq_intCast]`. Take the linear combination `hsq`. Establish `hwQ : IsIntegral ℚ w` using `hw.tower_top`. Establish `hmem' : y ∈ Algebra.adjoin ℚ {w}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hwQ.isAlgebraic]`.

Conclude with `hmem`. Establish `hrep : ∀ z ∈ Algebra.adjoin ℚ {w}, ∃ p q : ℚ, z = (p : K) + (q : K) * w`. Introduce `z hz`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Rewrite `hx` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by simp [hx]⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨p, q, rfl⟩` from `hx`.

Take `⟨r, s, rfl⟩` from `hz`. Conclude with `⟨p + r, q + s, by push_cast; ring⟩`. Consider the case `mul x z _ _ hx hz`. Take `⟨p, q, rfl⟩` from `hx`. Take `⟨r, s, rfl⟩` from `hz`.

Conclude with `⟨p * r - q * s * n, p * s + q * r + q * s * t, by push_cast; linear_combination (q : K) * (s : K) * hsq⟩`. Take `⟨p, q, hpq⟩` from `hrep y hmem'`. Establish `hσ : ∀ z : K, IsIntegral ℤ z → IsIntegral ℤ (z + σ z)` using `fun z hz => hz.add (hz.map σ.toIntAlgHom)`. Establish `hσw : σ w = (t : K) - w` using `by linear_combination ht`. Establish `hσy : σ y = (p : K) + (q : K) * ((t : K) - w)`.

Rewrite using `[hpq, map_add, map_mul, map_ratCast, map_ratCast, hσw]`. Establish `hA : y + σ y = ((2 * p + q * t : ℚ) : K)`. Rewrite using `[hσy, hpq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hB : w * y + σ (w * y) = ((p * t + q * (t ^ 2 - 2 * n) : ℚ) : K)`. Rewrite using `[map_mul, hσy, hσw, hpq]`. Use `push_cast`. Take the linear combination `2 * (q : K) * hsq`. Take `⟨A, hA'⟩` from `int_of_rat _ (hA ▸ hσ y hy)`.

Take `⟨B, hB'⟩` from `int_of_rat _ (hB ▸ hσ _ (hw.mul hy))`. Establish `hAK : (A : K) = 2 * p + q * t` using `by exact_mod_cast congrArg (Rat.cast : ℚ → K) hA'`. Establish `hBK : (B : K) = p * t + q * (t ^ 2 - 2 * n)`. Conclude with `congrArg (Rat.cast : ℚ → K) hB'` after adjusting the coercions. Use `⟨(t ^ 2 - 2 * n) * A - t * B, 2 * B - t * A, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[hAK, hBK, hpq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.discriminant_mul_integral_mem :
    ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* K) (w y : K) (t n : ℤ), w + σ w = (t : K) → w * σ w = (n : K) → IsIntegral ℤ y → y ∈ IntermediateField.adjoin ℚ {w} → ∃ a b : ℤ, ((t ^ 2 - 4 * n : ℤ) : K) * y = (a : K) + (b : K) * w := by
  intro K _ _ σ w y t n ht hn hy hmem
  have hsq : w * w = (t : K) * w - (n : K) := by linear_combination w * ht - hn
  have hw : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X,
        eq_intCast, eq_intCast]
      linear_combination hsq
  have hwQ : IsIntegral ℚ w := hw.tower_top
  have hmem' : y ∈ Algebra.adjoin ℚ {w} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hwQ.isAlgebraic]
    exact hmem
  have hrep : ∀ z ∈ Algebra.adjoin ℚ {w}, ∃ p q : ℚ, z = (p : K) + (q : K) * w := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p + r, q + s, by push_cast; ring⟩
    | mul x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p * r - q * s * n, p * s + q * r + q * s * t, by
        push_cast; linear_combination (q : K) * (s : K) * hsq⟩
  obtain ⟨p, q, hpq⟩ := hrep y hmem'
  have hσ : ∀ z : K, IsIntegral ℤ z → IsIntegral ℤ (z + σ z) := fun z hz =>
    hz.add (hz.map σ.toIntAlgHom)
  have hσw : σ w = (t : K) - w := by linear_combination ht
  have hσy : σ y = (p : K) + (q : K) * ((t : K) - w) := by
    rw [hpq, map_add, map_mul, map_ratCast, map_ratCast, hσw]
  have hA : y + σ y = ((2 * p + q * t : ℚ) : K) := by
    rw [hσy, hpq]; push_cast; ring
  have hB : w * y + σ (w * y) = ((p * t + q * (t ^ 2 - 2 * n) : ℚ) : K) := by
    rw [map_mul, hσy, hσw, hpq]; push_cast; linear_combination 2 * (q : K) * hsq
  obtain ⟨A, hA'⟩ := int_of_rat _ (hA ▸ hσ y hy)
  obtain ⟨B, hB'⟩ := int_of_rat _ (hB ▸ hσ _ (hw.mul hy))
  have hAK : (A : K) = 2 * p + q * t := by exact_mod_cast congrArg (Rat.cast : ℚ → K) hA'
  have hBK : (B : K) = p * t + q * (t ^ 2 - 2 * n) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → K) hB'
  refine ⟨(t ^ 2 - 2 * n) * A - t * B, 2 * B - t * A, ?_⟩
  push_cast
  rw [hAK, hBK, hpq]
  ring
