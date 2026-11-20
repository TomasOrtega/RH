import Mathlib

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `l hl Ω _ _ A m hm ζ hζ`. Establish `hpos : 0 < l ^ m` using `pow_pos hl.out.pos m`. Establish `memA : ∀ x : Ω, x ^ (l ^ m) = 1 → x ∈ A`. Introduce `x hx`. Break down `A.mem_or_inv_mem x with h | h` into its components or cases.

Conclude with `h`. Establish `h1 : x * x ^ (l ^ m - 1) = 1`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hpos]`. Conclude with `hx`. Establish `h2 : x⁻¹ = x ^ (l ^ m - 1)` using `inv_eq_of_mul_eq_one_right h1`.

Establish `h3 : x = (x⁻¹) ^ (l ^ m - 1)`. Rewrite using `[inv_pow, ← h2, inv_inv]`. Rewrite using `[h3]`. Conclude with `A.pow_mem h _`. Establish `key : ∀ x : Ω, x ∈ A → ∀ a : ℕ, A.valuation (x ^ a - 1) ≤ A.valuation (x - 1)`.

Introduce `x hx a`. Rewrite using `[← geom_sum_mul, map_mul]`. Establish `hs : A.valuation (∑ i ∈ Finset.range a, x ^ i) ≤ 1` using `(A.valuation_le_one_iff _).2 (sum_mem fun i _ => A.pow_mem hx i)`. Combine the equalities or inequalities in the displayed calculation. Establish `eqv : ∀ η ∈ primitiveRoots (l ^ m) Ω, A.valuation (1 - η) = A.valuation (ζ - 1)`.

Introduce `η hη`. Establish `hη' : IsPrimitiveRoot η (l ^ m)` using `(mem_primitiveRoots hpos).1 hη`. Rewrite using `[Valuation.map_sub_swap]`. Take `⟨a, -, ha⟩` from `hζ.eq_pow_of_pow_eq_one hη'.pow_eq_one`. Take `⟨b, -, hb⟩` from `hη'.eq_pow_of_pow_eq_one hζ.pow_eq_one`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← ha]`. Conclude with `key ζ (memA ζ hζ.pow_eq_one) a`. Rewrite using `[← hb]`. Conclude with `key η (memA η hη'.pow_eq_one) b`.

Establish `hprod : (l : Ω) = ∏ η ∈ primitiveRoots (l ^ m) Ω, (1 - η)`. Establish `e1` using `Polynomial.eval_one_cyclotomic_prime_pow (R := Ω) (p := l) (m - 1)`. Rewrite `e1` using `[Nat.sub_add_cancel hm, cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod]`. Simplify using `using e1.symm`. Rewrite using `[hprod, map_prod, Finset.prod_congr rfl eqv, Finset.prod_const, hζ.card_primitiveRoots]`.
-/
theorem valuation_primitiveRoot_sub_one_pow_totient :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ),
      1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) →
        A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  intro l hl Ω _ _ A m hm ζ hζ
  have hpos : 0 < l ^ m := pow_pos hl.out.pos m

  have memA : ∀ x : Ω, x ^ (l ^ m) = 1 → x ∈ A := by
    intro x hx
    rcases A.mem_or_inv_mem x with h | h
    · exact h
    · have h1 : x * x ^ (l ^ m - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hpos]; exact hx
      have h2 : x⁻¹ = x ^ (l ^ m - 1) := inv_eq_of_mul_eq_one_right h1
      have h3 : x = (x⁻¹) ^ (l ^ m - 1) := by
        rw [inv_pow, ← h2, inv_inv]
      rw [h3]; exact A.pow_mem h _
  have key : ∀ x : Ω, x ∈ A → ∀ a : ℕ, A.valuation (x ^ a - 1) ≤ A.valuation (x - 1) := by
    intro x hx a
    rw [← geom_sum_mul, map_mul]
    have hs : A.valuation (∑ i ∈ Finset.range a, x ^ i) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (sum_mem fun i _ => A.pow_mem hx i)
    calc _ ≤ 1 * A.valuation (x - 1) := by gcongr
      _ = _ := one_mul _
  have eqv : ∀ η ∈ primitiveRoots (l ^ m) Ω, A.valuation (1 - η) = A.valuation (ζ - 1) := by
    intro η hη
    have hη' : IsPrimitiveRoot η (l ^ m) := (mem_primitiveRoots hpos).1 hη
    rw [Valuation.map_sub_swap]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hη'.pow_eq_one
    obtain ⟨b, -, hb⟩ := hη'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← ha]; exact key ζ (memA ζ hζ.pow_eq_one) a
    · rw [← hb]; exact key η (memA η hη'.pow_eq_one) b
  have hprod : (l : Ω) = ∏ η ∈ primitiveRoots (l ^ m) Ω, (1 - η) := by
    have e1 := Polynomial.eval_one_cyclotomic_prime_pow (R := Ω) (p := l) (m - 1)
    rw [Nat.sub_add_cancel hm, cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at e1
    simpa using e1.symm
  rw [hprod, map_prod, Finset.prod_congr rfl eqv, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
