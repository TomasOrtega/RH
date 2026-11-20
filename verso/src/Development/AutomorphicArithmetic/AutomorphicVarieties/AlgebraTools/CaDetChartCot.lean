import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `B _ _ ι _ _ z m l c hx hl`. Establish `hmem` using `hx.mem`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Break down `k with i | j` into its components or cases.

Simplify using `only [Sum.elim_inl, Matrix.mulVec, dotProduct]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hmem (Sum.inl (i, j)))`. Simplify using `only [Sum.elim_inr]`. Conclude with `Ideal.sub_mem _ (hmem (Sum.inr j.1)) (Ideal.mul_mem_left _ _ (hmem (Sum.inr c)))`. Introduce `a ha`.

Set `b : ι × ι ⊕ ι → B` to `Sum.elim (fun ij => a (Sum.inl ij.1) * l ij.2) (fun j => if h : j = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩))`. Establish `key : ∑ k, b k * Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m k = ∑ k, a k * Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c) k`. Simplify using `only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[Fintype.sum_eq_add_sum_subtype_ne (fun j => b (Sum.inr j) * m j) c]`. Simplify using `only [b, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, dite_true]`.

Establish `e : ∀ j : {j // j ≠ c}, (if h : (j : ι) = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩)) * m j = a (Sum.inr j) * m j` using `fun j => by rw [dif_neg j.2]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => e j)]`. Establish `e2 : ∀ i, ∑ j, a (Sum.inl i) * l j * z i j = a (Sum.inl i) * ∑ j, z i j * l j`. Introduce `i`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`. Rewrite using `[Finset.sum_congr rfl (fun i _ => e2 i)]`. Establish `e3 : ∑ j : {j // j ≠ c}, a (Sum.inr j) * (m j - l j * m c) = ∑ j : {j // j ≠ c}, a (Sum.inr j) * m j - (∑ k : {k // k ≠ c}, a (Sum.inr k) * l k) * m c`. Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`.

Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ∀ k, b k ∈ maximalIdeal B` using `hx.indep b (by rw [key]; exact ha)`. Introduce `k`. Break down `k with i | j` into its components or cases.

Use `hb (Sum.inl (i, c))` as an intermediate fact. Simplify `this` using `[b, hl]`. Use `hb (Sum.inr j.1)` as an intermediate fact. Simplify `this` using `[b, j.2]`.
-/
theorem UpperTheory.V.AlgebraTools.chartGen_cotInd :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι B) (m l : ι → B) (c : ι),
      CotInd B (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → l c = 1 →
      CotInd B (Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c)) := by
  intro B _ _ ι _ _ z m l c hx hl
  have hmem := hx.mem
  refine ⟨?_, ?_⟩
  · intro k
    rcases k with i | j
    · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hmem (Sum.inl (i, j)))
    · simp only [Sum.elim_inr]
      exact Ideal.sub_mem _ (hmem (Sum.inr j.1)) (Ideal.mul_mem_left _ _ (hmem (Sum.inr c)))
  · intro a ha
    let b : ι × ι ⊕ ι → B := Sum.elim (fun ij => a (Sum.inl ij.1) * l ij.2)
      (fun j => if h : j = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1)
        else a (Sum.inr ⟨j, h⟩))
    have key : ∑ k, b k * Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m k
        = ∑ k, a k * Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c) k := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => b (Sum.inr j) * m j) c]
      simp only [b, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, dite_true]
      have e : ∀ j : {j // j ≠ c}, (if h : (j : ι) = c then
          -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩)) * m j
          = a (Sum.inr j) * m j := fun j => by rw [dif_neg j.2]
      rw [Finset.sum_congr rfl (fun j _ => e j)]
      have e2 : ∀ i, ∑ j, a (Sum.inl i) * l j * z i j = a (Sum.inl i) * ∑ j, z i j * l j := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun i _ => e2 i)]
      have e3 : ∑ j : {j // j ≠ c}, a (Sum.inr j) * (m j - l j * m c)
          = ∑ j : {j // j ≠ c}, a (Sum.inr j) * m j - (∑ k : {k // k ≠ c}, a (Sum.inr k) * l k) * m c := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e3]
      ring
    have hb : ∀ k, b k ∈ maximalIdeal B := hx.indep b (by rw [key]; exact ha)
    intro k
    rcases k with i | j
    · have := hb (Sum.inl (i, c))
      simpa [b, hl] using this
    · have := hb (Sum.inr j.1)
      simpa [b, j.2] using this
