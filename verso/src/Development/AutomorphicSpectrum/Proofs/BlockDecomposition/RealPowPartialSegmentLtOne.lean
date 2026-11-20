import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Segment

/- English proof (translation)
Take `⟨a, rfl⟩ : ∃ a, l₀ = a + 1` from `⟨l₀ - 1, by omega⟩`. Take `⟨b, rfl⟩ : ∃ b, l₁ = b + 1` from `⟨l₁ - 1, by omega⟩`. Rewrite using `[show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]`. Establish `hp : 2 * ((a + 1) * a / 2) = (a + 1) * a` using `Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self a)`. Establish `hq : 2 * ((a + b + 1 + 1) * (a + b + 1) / 2) = (a + b + 1 + 1) * (a + b + 1)` using `Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (a + b + 1))`.

Generalize the expression as in `(a + 1) * a / 2 = p at hp ⊢`. Generalize the expression as in `(a + b + 1 + 1) * (a + b + 1) / 2 = q at hq ⊢`. Use `zify at hp hq ⊢`. Take the linear combination `((d : ℤ) * (a + b + 1 + 1)) * hp - ((d : ℤ) * (a + 1)) * hq`.
-/
private theorem two_mul_triangle_add_mul_eq (d l₀ l₁ : ℕ) (h₀ : 1 ≤ l₀) (h₁ : 1 ≤ l₁) :
    2 * (d * (l₀ * l₁ + l₀ * (l₀ - 1) / 2)) * (l₀ + l₁) =
      2 * (d * ((l₀ + l₁) * (l₀ + l₁ - 1) / 2)) * l₀ + d * ((l₀ + l₁) * l₀ * l₁) := by
  obtain ⟨a, rfl⟩ : ∃ a, l₀ = a + 1 := ⟨l₀ - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, l₁ = b + 1 := ⟨l₁ - 1, by omega⟩
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hp : 2 * ((a + 1) * a / 2) = (a + 1) * a :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self a)
  have hq : 2 * ((a + b + 1 + 1) * (a + b + 1) / 2) = (a + b + 1 + 1) * (a + b + 1) :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (a + b + 1))
  generalize (a + 1) * a / 2 = p at hp ⊢
  generalize (a + b + 1 + 1) * (a + b + 1) / 2 = q at hq ⊢
  zify at hp hq ⊢
  linear_combination ((d : ℤ) * (a + b + 1 + 1)) * hp - ((d : ℤ) * (a + 1)) * hq

/- English proof (translation)
Introduce `α r d l0 l1 hα0 hα1 hr hd hl0 hl1 h`. Establish `key` using `two_mul_triangle_add_mul_eq d l0 l1 hl0 hl1`. Use `set T := (l0 + l1) * (l0 + l1 - 1) / 2`. Use `set S := l0 * l1 + l0 * (l0 - 1) / 2`. Establish `hpow : (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) = α ^ (d * ((l0 + l1) * l0 * l1))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]`. Apply the tactic sequence `congr 2 <;> ring`. Use `_ = (r ^ (l0 + l1) * α ^ (d * T)) ^ (2 * l0) * α ^ (d * ((l0 + l1) * l0 * l1)) := by`. Rewrite using `[key, pow_add α, mul_pow (r ^ (l0 + l1)), ← pow_mul α (d * T), show d * T * (2 * l0) = 2 * (d * T) * l0 by ring, ← mul_assoc ((r ^ (l0 + l1)) ^ (2 * l0))]`.

Use `_ = α ^ (d * ((l0 + l1) * l0 * l1)) := by rw [h, one_pow, one_mul]`. Establish `hlt : α ^ (d * ((l0 + l1) * l0 * l1)) < 1` using `pow_lt_one₀ hα0.le hα1 (Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).ne'`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : 1 ≤ (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1))` using `one_le_pow₀ hc`.

Rewrite `h1` using `[hpow]`. Conclude with `absurd hlt (not_lt.mpr h1)`.
-/
theorem top_piece_exponent_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 →
    r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 →
    r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  intro α r d l0 l1 hα0 hα1 hr hd hl0 hl1 h
  have key := two_mul_triangle_add_mul_eq d l0 l1 hl0 hl1
  set T := (l0 + l1) * (l0 + l1 - 1) / 2
  set S := l0 * l1 + l0 * (l0 - 1) / 2
  have hpow : (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) = α ^ (d * ((l0 + l1) * l0 * l1)) := by
    calc (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1))
        = (r ^ (l0 + l1)) ^ (2 * l0) * α ^ (2 * (d * S) * (l0 + l1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 2 <;> ring
      _ = (r ^ (l0 + l1) * α ^ (d * T)) ^ (2 * l0) * α ^ (d * ((l0 + l1) * l0 * l1)) := by
          rw [key, pow_add α, mul_pow (r ^ (l0 + l1)), ← pow_mul α (d * T),
            show d * T * (2 * l0) = 2 * (d * T) * l0 by ring, ← mul_assoc ((r ^ (l0 + l1)) ^ (2 * l0))]
      _ = α ^ (d * ((l0 + l1) * l0 * l1)) := by rw [h, one_pow, one_mul]
  have hlt : α ^ (d * ((l0 + l1) * l0 * l1)) < 1 :=
    pow_lt_one₀ hα0.le hα1
      (Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).ne'
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) := one_le_pow₀ hc
  rw [hpow] at h1
  exact absurd hlt (not_lt.mpr h1)

end GlobalTheory.CompanionTheory.Segment
