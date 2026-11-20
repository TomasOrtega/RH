import Mathlib

namespace PositivityTheory.Rg.Rs.StrStepA

/- English proof (translation)
Use `set e₁ : ℝ := ((d₁ : ℝ) - 1) / 2 with he₁`. Use `set e₂ : ℝ := ((d₂ : ℝ) - 1) / 2 with he₂`. Establish `hd₁' : (1 : ℝ) ≤ d₁` using `by exact_mod_cast hd₁`. Establish `hd₂' : (1 : ℝ) ≤ d₂` using `by exact_mod_cast hd₂`. Establish `he₁0 : 0 ≤ e₁` using `by rw [he₁]; linarith`.

Establish `he₂0 : 0 ≤ e₂` using `by rw [he₂]; linarith`. Establish `hcast₁ : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1` using `by rw [Nat.cast_sub hd₁]; simp`. Establish `hcast₂ : ((d₂ - 1 : ℕ) : ℝ) = d₂ - 1` using `by rw [Nat.cast_sub hd₂]; simp`. Use `set B : ℝ := c₁ + e₁ with hBdef`. Use `set C : ℝ := c₂ + e₂ - ((d₂ : ℝ) - 1) with hCdef`.

Establish `hB : B ∈ S` using `(hS _).2 (Or.inl ⟨0, hd₁, by simp [hBdef]⟩)`. Establish `hC : C ∈ S` using `(hS _).2 (Or.inr ⟨d₂ - 1, by omega, by rw [hcast₂]⟩)`. Establish `hmem : ∀ x ∈ S, x ≤ B ∨ C ≤ x`. Introduce `x hx`. Break down `(hS x).1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩` into its components or cases.

Use `left`. Establish `: (0 : ℝ) ≤ i` using `Nat.cast_nonneg i`. Combine the linear equalities and inequalities to obtain the conclusion. Use `right`. Establish `h1 : j ≤ d₂ - 1` using `by omega`.

Establish `h2 : (j : ℝ) ≤ ((d₂ - 1 : ℕ) : ℝ)` using `by exact_mod_cast h1`. Rewrite `h2` using `[hcast₂]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, hn⟩` from `hint _ hC _ hB`. Break down `lt_trichotomy n 1 with h | h | h` into its components or cases.

It suffices to derive a contradiction. Establish `hn0 : n ≤ 0` using `by omega`. Establish `hn0' : (n : ℝ) ≤ 0` using `by exact_mod_cast hn0`. Distinguish the cases in `hCA : c₁ - e₁ ≤ C`. Establish `hk : (((-n).toNat : ℕ) : ℤ) = -n` using `Int.toNat_of_nonneg (by omega)`.

Establish `hk' : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ)` using `by exact_mod_cast hk`. Establish `hkd : (-n).toNat < d₁`. Establish `: (((-n).toNat : ℕ) : ℝ) < d₁` using `by rw [hk']; linarith`. Conclude with `this` after adjusting the coercions. Use `hdisj (-n).toNat (d₂ - 1) hkd (by omega) ?_` and prove the remaining obligations.

Rewrite using `[hk', hcast₂]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hCA` using `[not_le]`. Establish `hJ0 : (0 : ℤ) ≤ n + d₁ + d₂ - 2`. Establish `: (0 : ℝ) ≤ (n : ℝ) + d₁ + d₂ - 2` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `hJ1 : n + d₁ + d₂ - 2 < (d₂ : ℤ)`. Establish `: (n : ℝ) + d₁ + d₂ - 2 < d₂` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hj : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℤ) = n + d₁ + d₂ - 2` using `Int.toNat_of_nonneg hJ0`.

Establish `hj' : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℝ) = (n : ℝ) + d₁ + d₂ - 2` using `by exact_mod_cast hj`. Establish `hjd : (n + d₁ + d₂ - 2).toNat < d₂` using `by omega`. Use `hdisj (d₁ - 1) (n + d₁ + d₂ - 2).toNat (by omega) hjd ?_` and prove the remaining obligations. Rewrite using `[hj', hcast₁]`. Combine the linear equalities and inequalities to obtain the conclusion.

Substitute `h` using the available equality. Move the coercions through the operations in `at hn`. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Establish `hn2 : (2 : ℝ) ≤ n` using `by exact_mod_cast (show (2 : ℤ) ≤ n by omega)`.

Apply the tactic sequence `have hC1 : C - 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith`. Apply the tactic sequence `have hB1 : B + 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith`. Establish `hClt : C < 1`. Assume the negation of the conclusion as `h3`. Conclude with `hC1 (hP _ hC (not_lt.1 h3))`.

Establish `hBgt : -1 < B`. Assume the negation of the conclusion as `h3`. Rewrite `h3` using `[not_lt]`. Establish `h4` using `hneg _ (hP _ (hneg _ hB) (by linarith))`. Conclude with `hB1 (by convert h4 using 1; ring)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem adjacent (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (S : Set ℝ)
    (hS : ∀ x, x ∈ S ↔ (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨
      ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hdisj : ∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n)
    (hneg : ∀ x ∈ S, -x ∈ S) (hP : ∀ u ∈ S, 1 ≤ u → u - 1 ∈ S) (hc : c₁ < c₂) :
    c₂ - c₁ = ((d₁ : ℝ) + d₂) / 2 := by
  set e₁ : ℝ := ((d₁ : ℝ) - 1) / 2 with he₁
  set e₂ : ℝ := ((d₂ : ℝ) - 1) / 2 with he₂
  have hd₁' : (1 : ℝ) ≤ d₁ := by exact_mod_cast hd₁
  have hd₂' : (1 : ℝ) ≤ d₂ := by exact_mod_cast hd₂
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; linarith
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; linarith
  have hcast₁ : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub hd₁]; simp
  have hcast₂ : ((d₂ - 1 : ℕ) : ℝ) = d₂ - 1 := by rw [Nat.cast_sub hd₂]; simp
  set B : ℝ := c₁ + e₁ with hBdef
  set C : ℝ := c₂ + e₂ - ((d₂ : ℝ) - 1) with hCdef
  have hB : B ∈ S := (hS _).2 (Or.inl ⟨0, hd₁, by simp [hBdef]⟩)
  have hC : C ∈ S := (hS _).2 (Or.inr ⟨d₂ - 1, by omega, by rw [hcast₂]⟩)
  have hmem : ∀ x ∈ S, x ≤ B ∨ C ≤ x := by
    intro x hx
    rcases (hS x).1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · left; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    · right
      have h1 : j ≤ d₂ - 1 := by omega
      have h2 : (j : ℝ) ≤ ((d₂ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hcast₂] at h2; linarith
  obtain ⟨n, hn⟩ := hint _ hC _ hB
  rcases lt_trichotomy n 1 with h | h | h
  · exfalso
    have hn0 : n ≤ 0 := by omega
    have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    by_cases hCA : c₁ - e₁ ≤ C
    · have hk : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have hk' : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast hk
      have hkd : (-n).toNat < d₁ := by
        have : (((-n).toNat : ℕ) : ℝ) < d₁ := by rw [hk']; linarith
        exact_mod_cast this
      refine hdisj (-n).toNat (d₂ - 1) hkd (by omega) ?_
      rw [hk', hcast₂]; linarith
    · rw [not_le] at hCA
      have hJ0 : (0 : ℤ) ≤ n + d₁ + d₂ - 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) + d₁ + d₂ - 2 := by linarith
        exact_mod_cast this
      have hJ1 : n + d₁ + d₂ - 2 < (d₂ : ℤ) := by
        have : (n : ℝ) + d₁ + d₂ - 2 < d₂ := by linarith
        exact_mod_cast this
      have hj : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℤ) = n + d₁ + d₂ - 2 := Int.toNat_of_nonneg hJ0
      have hj' : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℝ) = (n : ℝ) + d₁ + d₂ - 2 := by exact_mod_cast hj
      have hjd : (n + d₁ + d₂ - 2).toNat < d₂ := by omega
      refine hdisj (d₁ - 1) (n + d₁ + d₂ - 2).toNat (by omega) hjd ?_
      rw [hj', hcast₁]; linarith
  · subst h
    push_cast at hn
    linarith
  · exfalso
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
    have hC1 : C - 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hB1 : B + 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hClt : C < 1 := by
      by_contra h3; exact hC1 (hP _ hC (not_lt.1 h3))
    have hBgt : -1 < B := by
      by_contra h3; rw [not_lt] at h3
      have h4 := hneg _ (hP _ (hneg _ hB) (by linarith))
      exact hB1 (by convert h4 using 1; ring)
    linarith

end PositivityTheory.Rg.Rs.StrStepA
