import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

/- English proof (translation)
Rewrite using `[← Finset.sum_image (g := f) (f := g) hf]`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hg s hs)` and prove the remaining obligations. Introduce `s hs`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `hS t ht`.
-/
theorem sum_comp_le_sum_of_injOn {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S) (hg : ∀ s ∈ S, 0 ≤ g s) :
    ∑ t ∈ T, g (f t) ≤ ∑ s ∈ S, g s := by
  rw [← Finset.sum_image (g := f) (f := g) hf]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hg s hs)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
  exact hS t ht

/- English proof (translation)
Establish `h1` using `Finset.sum_le_sum hu`. Rewrite `h1` using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]`. Establish `h2` using `sum_comp_le_sum_of_injOn T S f g hf hS hg`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_le_sum_add_card_mul {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (u : ι → ℝ) (c : ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S)
    (hg : ∀ s ∈ S, 0 ≤ g s) (hu : ∀ t ∈ T, u t ≤ g (f t) + c) :
    ∑ t ∈ T, u t ≤ ∑ s ∈ S, g s + (T.card : ℝ) * c := by
  have h1 := Finset.sum_le_sum hu
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 := sum_comp_le_sum_of_injOn T S f g hf hS hg
  linarith

/- English proof (translation)
Introduce `e p q e0 h0 he hle v a n0 er her H hsym`. Use `set S : Finset ℤ := Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ) with hS`. Establish `hmem : ∀ s : ℤ, s ∈ S ↔ 1 ≤ s ∧ s ≤ (h0 : ℤ) + p + q`. Introduce `s`. Simplify using `[hS]`.

Establish `ha : ∀ s ∈ S, 0 ≤ a s` using `fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).1`. Establish `hn : ∀ s ∈ S, 0 ≤ n0 s` using `fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).2.1`. Establish `hsplit : ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s = ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s + ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s`. Rewrite using `[← Finset.sum_union]`. Use `congr 1`.

Use extensionality with `s`. Simplify using `only [mem_union, mem_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `s h1 h2`.

Simplify using `only [mem_Icc] at h1 h2`. Use linear arithmetic over natural numbers and integers. Establish `b1 : ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s ≤ ∑ s ∈ S, a s + (e0 : ℝ) * er`. Use `sum_le_sum_add_card_mul (Icc (1 - (e0 : ℤ)) 0) S (fun s => 1 - s) a v er (fun x _ y _ h => by simpa using h) (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha (fun t ht => by` as an intermediate fact. Simplify using `only [mem_Icc] at ht`.

Rewrite using `[hsym t ht.1 ht.2]`. Conclude with `(H _ (by omega) (by omega)).2.2.1)`. Establish `hc : (Icc (1 - (e0 : ℤ)) 0).card = e0`. Rewrite using `[Int.card_Icc]`. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[hc]`. Then use the resulting hypothesis. Establish `b2 : ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s ≤ ∑ s ∈ S, a s + (h0 : ℝ) * er`. Use `sum_le_sum_add_card_mul (Icc (1 : ℤ) (h0 : ℤ)) S (fun s => s) a v er (fun x _ y _ h => h) (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha (fun t ht => by` as an intermediate fact. Simplify using `only [mem_Icc] at ht`. Conclude with `(H _ (by omega) (by omega)).2.2.1)`.

Establish `hc : (Icc (1 : ℤ) (h0 : ℤ)).card = h0`. Rewrite using `[Int.card_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite `this` using `[hc]`. Then use the resulting hypothesis. Establish `b3 : ∑ k ∈ range p, v ((e : ℤ) + q - k) ≤ ∑ s ∈ S, a s + (p : ℝ) * er`.

Use `sum_le_sum_add_card_mul (range p) S (fun k : ℕ => (e : ℤ) + q - k) a (fun k : ℕ => v ((e : ℤ) + q - k)) er (fun x _ y _ h => by simp only at h; omega) (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) ha (fun t ht => by` as an intermediate fact. Simplify using `only [mem_range] at ht`. Conclude with `(H _ (by omega) (by omega)).2.2.1)`. Rewrite `this` using `[card_range]`. Then use the resulting hypothesis. Establish `b4 : ∑ k ∈ range q, -v ((e : ℤ) + k + 1) ≤ ∑ s ∈ S, (a s + n0 s) + (q : ℝ) * 0`.

Use `sum_le_sum_add_card_mul (range q) S (fun k : ℕ => (e : ℤ) + k + 1) (fun s => a s + n0 s) (fun k : ℕ => -v ((e : ℤ) + k + 1)) 0 (fun x _ y _ h => by simp only at h; omega) (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) (fun s hs => add_nonneg (ha s hs) (hn s hs)) ( …` as an intermediate fact. Simplify using `only [mem_range] at ht`. Rewrite using `[add_zero]`. Conclude with `(H _ (by omega) (by omega)).2.2.2)`. Rewrite `this` using `[card_range]`. Then use the resulting hypothesis.

Rewrite `b4` using `[Finset.sum_neg_distrib, Finset.sum_add_distrib]`. Establish `hN : 0 ≤ ∑ s ∈ S, n0 s` using `Finset.sum_nonneg hn`. Establish `hA : 0 ≤ ∑ s ∈ S, a s` using `Finset.sum_nonneg ha`. Establish `hcount : ((e0 : ℝ) + h0 + p) * er ≤ ((2 * (h0 + p + q) : ℕ) : ℝ) * er`. Use `mul_le_mul_of_nonneg_right ?_ her` and prove the remaining obligations.

Establish `: e0 + h0 + p ≤ 2 * (h0 + p + q)` using `by omega`. Conclude with `this` after adjusting the coercions. Rewrite using `[hsplit]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem count_factors : ∀ (e p q e0 h0 : ℕ), e0 + p = e + q → e0 ≤ h0 → ∀ (v a n0 : ℤ → ℝ) (er : ℝ), 0 ≤ er → (∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q → 0 ≤ a s ∧ 0 ≤ n0 s ∧ v s ≤ a s + er ∧ -(v s) ≤ a s + n0 s) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → v s = v (1 - s)) → (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s) + (∑ k ∈ range p, v ((e : ℤ) + q - k)) - (∑ k ∈ range q, v ((e : ℤ) + k + 1)) ≤ 4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) + ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
  intro e p q e0 h0 he hle v a n0 er her H hsym
  set S : Finset ℤ := Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ) with hS
  have hmem : ∀ s : ℤ, s ∈ S ↔ 1 ≤ s ∧ s ≤ (h0 : ℤ) + p + q := by
    intro s; simp [hS]
  have ha : ∀ s ∈ S, 0 ≤ a s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).1
  have hn : ∀ s ∈ S, 0 ≤ n0 s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).2.1
  have hsplit : ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s
      = ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s + ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s := by
    rw [← Finset.sum_union]
    · congr 1
      ext s
      simp only [mem_union, mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro s h1 h2
      simp only [mem_Icc] at h1 h2
      omega
  have b1 : ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s ≤ ∑ s ∈ S, a s + (e0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 - (e0 : ℤ)) 0) S (fun s => 1 - s) a v er
      (fun x _ y _ h => by simpa using h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        rw [hsym t ht.1 ht.2]
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 - (e0 : ℤ)) 0).card = e0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b2 : ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s ≤ ∑ s ∈ S, a s + (h0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 : ℤ) (h0 : ℤ)) S (fun s => s) a v er
      (fun x _ y _ h => h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 : ℤ) (h0 : ℤ)).card = h0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b3 : ∑ k ∈ range p, v ((e : ℤ) + q - k) ≤ ∑ s ∈ S, a s + (p : ℝ) * er := by
    have := sum_le_sum_add_card_mul (range p) S (fun k : ℕ => (e : ℤ) + q - k) a
      (fun k : ℕ => v ((e : ℤ) + q - k)) er
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) ha
      (fun t ht => by
        simp only [mem_range] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    rwa [card_range] at this
  have b4 : ∑ k ∈ range q, -v ((e : ℤ) + k + 1) ≤ ∑ s ∈ S, (a s + n0 s) + (q : ℝ) * 0 := by
    have := sum_le_sum_add_card_mul (range q) S (fun k : ℕ => (e : ℤ) + k + 1)
      (fun s => a s + n0 s) (fun k : ℕ => -v ((e : ℤ) + k + 1)) 0
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega)
      (fun s hs => add_nonneg (ha s hs) (hn s hs))
      (fun t ht => by
        simp only [mem_range] at ht
        rw [add_zero]
        exact (H _ (by omega) (by omega)).2.2.2)
    rwa [card_range] at this
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at b4
  have hN : 0 ≤ ∑ s ∈ S, n0 s := Finset.sum_nonneg hn
  have hA : 0 ≤ ∑ s ∈ S, a s := Finset.sum_nonneg ha
  have hcount : ((e0 : ℝ) + h0 + p) * er ≤ ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
    refine mul_le_mul_of_nonneg_right ?_ her
    have : e0 + h0 + p ≤ 2 * (h0 + p + q) := by omega
    exact_mod_cast this
  rw [hsplit]
  linarith

end GlobalTheory.Square
