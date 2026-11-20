import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Establish `hpow : maximalIdeal R ^ n = (maximalIdeal A ^ n).map φ`. Rewrite using `[Ideal.map_pow, hm]`. Rewrite `hx` using `[hpow]`. Unfold `Ideal.map at hx`. Use `Submodule.span_induction (p := fun x _ => ∃ P : Polynomial A, Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧ x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1)) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `⟨Polynomial.C a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_C, hpow]`. Conclude with `Ideal.mem_map_of_mem φ ha`. Simplify using the standard rewrite rules.

Conclude with `⟨0, by simp, by simp⟩`. Introduce and unpack `x y _ _ ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩`. Use `⟨P + Q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_add]`. Conclude with `add_mem hP hQ`.

Establish `: x + y - Polynomial.eval₂ φ θ (P + Q) = (x - Polynomial.eval₂ φ θ P) + (y - Polynomial.eval₂ φ θ Q)`. Rewrite using `[Polynomial.eval₂_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem hxP hyQ`.

Introduce and unpack `r x _ ⟨P, hP, hxP⟩`. Take `⟨Q, hQ⟩` from `h1 r`. Use `⟨Q * P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_mul]`. Conclude with `Ideal.mul_mem_left _ _ hP`.

Establish `: r • x - Polynomial.eval₂ φ θ (Q * P) = r * (x - Polynomial.eval₂ φ θ P) + (r - Polynomial.eval₂ φ θ Q) * Polynomial.eval₂ φ θ P`. Rewrite using `[Polynomial.eval₂_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `add_mem (Ideal.mul_mem_left _ _ hxP) ?_` and prove the remaining obligations.

Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul hQ hP`.
-/
theorem exists_eval₂_approx_maximalIdeal_pow_succ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hm : (maximalIdeal A).map φ = maximalIdeal R) (θ : R)
    (h1 : ∀ r : R, ∃ P : Polynomial A, r - Polynomial.eval₂ φ θ P ∈ maximalIdeal R)
    (n : ℕ) (x : R) (hx : x ∈ maximalIdeal R ^ n) :
    ∃ P : Polynomial A, Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1) := by
  have hpow : maximalIdeal R ^ n = (maximalIdeal A ^ n).map φ := by
    rw [Ideal.map_pow, hm]
  rw [hpow] at hx
  unfold Ideal.map at hx
  refine Submodule.span_induction (p := fun x _ => ∃ P : Polynomial A,
      Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Polynomial.C a, ?_, ?_⟩
    · rw [Polynomial.eval₂_C, hpow]; exact Ideal.mem_map_of_mem φ ha
    · simp
  · exact ⟨0, by simp, by simp⟩
  · rintro x y _ _ ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
    refine ⟨P + Q, ?_, ?_⟩
    · rw [Polynomial.eval₂_add]; exact add_mem hP hQ
    · have : x + y - Polynomial.eval₂ φ θ (P + Q) =
          (x - Polynomial.eval₂ φ θ P) + (y - Polynomial.eval₂ φ θ Q) := by
        rw [Polynomial.eval₂_add]; ring
      rw [this]; exact add_mem hxP hyQ
  · rintro r x _ ⟨P, hP, hxP⟩
    obtain ⟨Q, hQ⟩ := h1 r
    refine ⟨Q * P, ?_, ?_⟩
    · rw [Polynomial.eval₂_mul]; exact Ideal.mul_mem_left _ _ hP
    · have : r • x - Polynomial.eval₂ φ θ (Q * P) =
          r * (x - Polynomial.eval₂ φ θ P) +
            (r - Polynomial.eval₂ φ θ Q) * Polynomial.eval₂ φ θ P := by
        rw [Polynomial.eval₂_mul, smul_eq_mul]; ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ hxP) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hQ hP

/- English proof (translation)
Introduce `A R _ _ _ _ φ hm θ h1 n r`. Simplify using `only [Polynomial.eval_map] at h1 ⊢`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`.

Take `⟨P, hP⟩` from `ih`. Take `⟨Q, -, hQ⟩` from `exists_eval₂_approx_maximalIdeal_pow_succ φ hm θ h1 n _ hP`. Use `⟨P + Q, ?_⟩` and prove the remaining obligations. Establish `: r - Polynomial.eval₂ φ θ (P + Q) = r - Polynomial.eval₂ φ θ P - Polynomial.eval₂ φ θ Q`. Rewrite using `[Polynomial.eval₂_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hQ`.
-/
theorem exists_poly_sub_mem_maximalIdeal_pow : ∀ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R →
    ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) →
    ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  intro A R _ _ _ _ φ hm θ h1 n r
  simp only [Polynomial.eval_map] at h1 ⊢
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, -, hQ⟩ := exists_eval₂_approx_maximalIdeal_pow_succ φ hm θ h1 n _ hP
    refine ⟨P + Q, ?_⟩
    have : r - Polynomial.eval₂ φ θ (P + Q) =
        r - Polynomial.eval₂ φ θ P - Polynomial.eval₂ φ θ Q := by
      rw [Polynomial.eval₂_add]; ring
    rw [this]; exact hQ

end GlobalTheory
