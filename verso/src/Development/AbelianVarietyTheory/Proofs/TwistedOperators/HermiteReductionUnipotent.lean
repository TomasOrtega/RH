import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Use `⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩` and prove the remaining obligations. Conclude with `absurd (Fin.lt_def.1 hi) (by omega)`. Consider the case `succ m ih`.

Take `⟨x, hx1, hx0, hx⟩` from `ih`. Distinguish the cases in `h : ∃ k : Fin n, (j : ℕ) = k + m + 1`. Take `⟨k, hk⟩` from `h`. Take `⟨z, hz⟩` from `hr k (b.mulVec x k)`. Establish `hkj : k < j` using `Fin.lt_def.2 (by omega)`.

Establish `key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z`. Introduce `i`. Rewrite using `[Matrix.mulVec_sub, Pi.sub_apply]`. Use `congr 1`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Use `⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩` and prove the remaining obligations. Simplify using `[hx1, hkj.ne']`. Simplify using `[hx0 l hl, (hkj.trans hl).ne']`. Rewrite using `[key]`. Distinguish the cases in `hik : i = k`.

Substitute `hik` using the available equality. Conclude with `⟨b.mulVec x i, by rw [← hz]; ring⟩`. Establish `hne : (i : ℕ) ≠ k` using `fun e => hik (Fin.ext e)`. Establish `hki : k < i` using `Fin.lt_def.2 (by omega)`. Rewrite using `[hb i k hki, zero_mul, sub_zero]`.

Conclude with `hx i hi (by omega)`. Use `⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `h ⟨i, by omega⟩`.
-/
theorem hermite_reduction_column {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R → R) (hb : ∀ i j, j < i → b i j = 0) (hr : ∀ i y, b i i ∣ y - r i y)
    (j : Fin n) (m : ℕ) :
    ∃ x : Fin n → R, x j = 1 ∧ (∀ l, j < l → x l = 0) ∧
      ∀ i : Fin n, i < j → (j : ℕ) ≤ i + m → ∃ y, b.mulVec x i = r i y := by
  induction m with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩
    exact absurd (Fin.lt_def.1 hi) (by omega)
  | succ m ih =>
    obtain ⟨x, hx1, hx0, hx⟩ := ih
    by_cases h : ∃ k : Fin n, (j : ℕ) = k + m + 1
    · obtain ⟨k, hk⟩ := h
      obtain ⟨z, hz⟩ := hr k (b.mulVec x k)
      have hkj : k < j := Fin.lt_def.2 (by omega)
      have key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z := by
        intro i
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      refine ⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩
      · simp [hx1, hkj.ne']
      · simp [hx0 l hl, (hkj.trans hl).ne']
      · rw [key]
        by_cases hik : i = k
        · subst hik
          exact ⟨b.mulVec x i, by rw [← hz]; ring⟩
        · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
          have hki : k < i := Fin.lt_def.2 (by omega)
          rw [hb i k hki, zero_mul, sub_zero]
          exact hx i hi (by omega)
    · refine ⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩
      by_contra hc
      exact h ⟨i, by omega⟩

/- English proof (translation)
Introduce `R _ n b r hb hr`. Use `choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n`. Use `⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx j i h (by have := j.2; omega)`. Conclude with `⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩`.
-/
theorem hermite_reduction_unipotent :
    ∀ (R : Type) [CommRing R] (n : ℕ) (b : Matrix (Fin n) (Fin n) R) (r : Fin n → R → R),
      (∀ i j, j < i → b i j = 0) → (∀ i y, b i i ∣ y - r i y) →
      ∃ u : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        ∀ i j, i < j → ∃ y, (b * u) i j = r i y := by
  intro R _ n b r hb hr
  choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n
  refine ⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩
  obtain ⟨y, hy⟩ := hx j i h (by have := j.2; omega)
  exact ⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩

end GlobalTheory
