import Mathlib

/- English proof (translation)
Introduce `R _ x α β A B hA hB r`. Take `⟨NA, hNA⟩` from `hA r`. Take `⟨NB, hNB⟩` from `hB r`. Establish `hα : ∀ p ≥ NA, x ^ r ∣ α p`. Introduce `p hp`.

Establish `h1` using `hNA p hp`. Establish `h2` using `hNA (p + 1) (by omega)`. Establish `e : α p = (A - ∑ i ∈ Finset.range p, α i) - (A - ∑ i ∈ Finset.range (p + 1), α i)`. Rewrite using `[Finset.sum_range_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `dvd_sub h1 h2`. Use `⟨NA + NB, fun n hn => ?_⟩` and prove the remaining obligations. Establish `key : ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) = ∑ p ∈ Finset.range n, α p * ∑ q ∈ Finset.range (n - p), β q`. Rewrite using `[Finset.sum_range_diag_flip n (fun p q => α p * β q)]`.

Simplify using `only [Finset.mul_sum]`. Establish `hsplit : A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) = (A - ∑ p ∈ Finset.range n, α p) * B + ∑ p ∈ Finset.range n, α p * (B - ∑ q ∈ Finset.range (n - p), β q)`. Rewrite using `[key, Finset.sum_congr rfl (fun p _ => mul_sub (α p) B _), Finset.sum_sub_distrib, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`.

Use `dvd_add (dvd_mul_of_dvd_left (hNA n (by omega)) _) (Finset.dvd_sum fun p _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hp' : NA ≤ p`. Conclude with `dvd_mul_of_dvd_left (hα p hp') _`. Conclude with `dvd_mul_of_dvd_right (hNB _ (by omega)) _`.
-/
theorem GlobalTheory.cauchy_product_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  intro R _ x α β A B hA hB r
  obtain ⟨NA, hNA⟩ := hA r
  obtain ⟨NB, hNB⟩ := hB r
  have hα : ∀ p ≥ NA, x ^ r ∣ α p := by
    intro p hp
    have h1 := hNA p hp
    have h2 := hNA (p + 1) (by omega)
    have e : α p = (A - ∑ i ∈ Finset.range p, α i) - (A - ∑ i ∈ Finset.range (p + 1), α i) := by
      rw [Finset.sum_range_succ]; ring
    rw [e]; exact dvd_sub h1 h2
  refine ⟨NA + NB, fun n hn => ?_⟩
  have key : ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = ∑ p ∈ Finset.range n, α p * ∑ q ∈ Finset.range (n - p), β q := by
    rw [Finset.sum_range_diag_flip n (fun p q => α p * β q)]
    simp only [Finset.mul_sum]
  have hsplit : A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = (A - ∑ p ∈ Finset.range n, α p) * B
        + ∑ p ∈ Finset.range n, α p * (B - ∑ q ∈ Finset.range (n - p), β q) := by
    rw [key, Finset.sum_congr rfl (fun p _ => mul_sub (α p) B _), Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  rw [hsplit]
  refine dvd_add (dvd_mul_of_dvd_left (hNA n (by omega)) _) (Finset.dvd_sum fun p _ => ?_)
  by_cases hp' : NA ≤ p
  · exact dvd_mul_of_dvd_left (hα p hp') _
  · exact dvd_mul_of_dvd_right (hNB _ (by omega)) _
