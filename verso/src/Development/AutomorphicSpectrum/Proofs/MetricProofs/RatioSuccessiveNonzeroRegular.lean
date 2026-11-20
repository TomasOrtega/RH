import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.UnitQuotients

/- English proof (translation)
Introduce `Φ _ R N G E hE hU i`. Distinguish the cases in `h : (i : ℕ) = 0`. Establish `hI : Finset.Iic i = {i}`. Use extensionality with `k`. Simplify using `only [Finset.mem_Iic, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce `hk`. Apply `Fin.ext` to reduce the goal to its premises. Establish `: (k : ℕ) ≤ i` using `hk`. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `rfl`. Conclude with `le_rfl`. Establish `hi` using `hU i`. Rewrite `hi` using `[hI, Finset.prod_singleton]`. Simplify `hi` using `only [dif_pos h]`.

Simplify using `only [dif_neg h]`. Establish `hlt : (i : ℕ) - 1 < N` using `by have := i.2; omega`. Generalize the expression as in `hj : (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = j`. Establish `hjv : (j : ℕ) = (i : ℕ) - 1` using `by rw [← hj]`. Establish `hI : Finset.Iic i = insert i (Finset.Iic j)`.

Use extensionality with `k`. Simplify using `only [Finset.mem_Iic, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Establish `hk' : (k : ℕ) ≤ i` using `hk`.

Distinguish the cases in `hki : k = i`. Conclude with `Or.inl hki`. Use `right`. Establish `: (k : ℕ) ≠ i` using `fun e => hki (Fin.ext e)`. Use `show (k : ℕ) ≤ j`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `(rfl | hk)`. Conclude with `le_rfl`. Establish `hk' : (k : ℕ) ≤ j` using `hk show (k : ℕ) ≤ i`. Use linear arithmetic over natural numbers and integers.

Establish `hnot : i ∉ Finset.Iic j`. Simplify using `only [Finset.mem_Iic]`. Introduce `hij`. Establish `: (i : ℕ) ≤ j` using `hij`. Use linear arithmetic over natural numbers and integers.

Take `⟨a0, a1, a2⟩` from `hU i`. Take `⟨b0, b1, b2⟩` from `hU j`. Rewrite `a0`, `a1`, `a2` using `[hI, Finset.prod_insert hnot]`. Generalize the expression as in `(∏ k ∈ Finset.Iic j, G k) = D at a0 a1 a2 b0 b1 b2`. Establish `hD : D ≠ 0` using `fun e => b0 (by rw [e, zero_div])`.

Establish `hEi` using `hE i`. Establish `hEj` using `hE j`. Establish `key : G i / (E i / E j) = (G i * D / E i) * (D / E j)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`.

Use `⟨mul_ne_zero a0 (inv_ne_zero b0), R.mul_mem a1 b2, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv, inv_inv]`. Conclude with `R.mul_mem a2 b1`.
-/
theorem consecutive_quotients_units :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (N : ℕ) (G E : Fin N → Φ), (∀ i, E i ≠ 0) → (∀ i, (∏ k ∈ Finset.Iic i, G k) / E i ≠ 0 ∧ (∏ k ∈ Finset.Iic i, G k) / E i ∈ R ∧ ((∏ k ∈ Finset.Iic i, G k) / E i)⁻¹ ∈ R) → ∀ i : Fin N, G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ≠ 0 ∧ G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ∈ R ∧ (G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩))⁻¹ ∈ R := by
  intro Φ _ R N G E hE hU i
  by_cases h : (i : ℕ) = 0
  · have hI : Finset.Iic i = {i} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      constructor
      · intro hk
        apply Fin.ext
        have : (k : ℕ) ≤ i := hk
        omega
      · rintro rfl
        exact le_rfl
    have hi := hU i
    rw [hI, Finset.prod_singleton] at hi
    simpa only [dif_pos h] using hi
  · simp only [dif_neg h]
    have hlt : (i : ℕ) - 1 < N := by have := i.2; omega
    generalize hj : (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = j
    have hjv : (j : ℕ) = (i : ℕ) - 1 := by rw [← hj]
    have hI : Finset.Iic i = insert i (Finset.Iic j) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro hk
        have hk' : (k : ℕ) ≤ i := hk
        by_cases hki : k = i
        · exact Or.inl hki
        · right
          have : (k : ℕ) ≠ i := fun e => hki (Fin.ext e)
          show (k : ℕ) ≤ j
          omega
      · rintro (rfl | hk)
        · exact le_rfl
        · have hk' : (k : ℕ) ≤ j := hk
          show (k : ℕ) ≤ i
          omega
    have hnot : i ∉ Finset.Iic j := by
      simp only [Finset.mem_Iic]
      intro hij
      have : (i : ℕ) ≤ j := hij
      omega
    obtain ⟨a0, a1, a2⟩ := hU i
    obtain ⟨b0, b1, b2⟩ := hU j
    rw [hI, Finset.prod_insert hnot] at a0 a1 a2
    generalize (∏ k ∈ Finset.Iic j, G k) = D at a0 a1 a2 b0 b1 b2
    have hD : D ≠ 0 := fun e => b0 (by rw [e, zero_div])
    have hEi := hE i
    have hEj := hE j
    have key : G i / (E i / E j) = (G i * D / E i) * (D / E j)⁻¹ := by
      field_simp
    rw [key]
    refine ⟨mul_ne_zero a0 (inv_ne_zero b0), R.mul_mem a1 b2, ?_⟩
    rw [mul_inv, inv_inv]
    exact R.mul_mem a2 b1

end GlobalTheory.CompanionTheory.Metric.UnitQuotients
