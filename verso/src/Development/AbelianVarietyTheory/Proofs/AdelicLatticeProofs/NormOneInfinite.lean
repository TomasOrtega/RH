import Mathlib

namespace GlobalTheory.NormOneInfinite

/- English proof (translation)
Establish `hx : ∃ x : E, c x ≠ x`. Assume the negation of the conclusion as `hall`. Simplify using `only [ne_eq, not_exists, not_not] at hall`. Conclude with `h1 (AlgEquiv.ext fun x => by rw [hall x, AlgEquiv.one_apply])`. Take `⟨x, hx⟩` from `hx`.

Establish `hcd : c (x - c x) = -(x - c x)`. Rewrite using `[map_sub, hc x]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : x - c x ≠ 0` using `sub_ne_zero.mpr (Ne.symm hx)`. Establish `hcn : ∀ n : ℕ, c (n : E) = n` using `fun n => map_natCast c n`.

Establish `h2d : ∀ y : E, y = -y → y = 0`. Introduce `y hy`. Establish `h2 : (2 : E) * y = 0` using `by linear_combination hy`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `absurd h two_ne_zero`.

Conclude with `h`. Establish `hsub : ∀ n : ℕ, (n : E) - (x - c x) ≠ 0`. Introduce `n h0`. Establish `e : x - c x = n` using `(sub_eq_zero.mp h0).symm`. Apply `hd` to reduce the goal to its premises.

Apply `h2d` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hadd : ∀ n : ℕ, (n : E) + (x - c x) ≠ 0`. Introduce `n h0`. Establish `e : x - c x = -(n : E)` using `by linear_combination h0`.

Apply `hd` to reduce the goal to its premises. Apply `h2d` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : E) + (x - c x)) / ((n : E) - (x - c x))) ?_ ?_` and prove the remaining obligations. Introduce `n m hnm`.

Simplify using `only at hnm`. Rewrite `hnm` using `[div_eq_div_iff (hsub n) (hsub m)]`. Establish `h3 : (2 : E) * (x - c x) * ((m : E) - n) = 0` using `by linear_combination hnm`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Break down `mul_eq_zero.mp h with h' | h'` into its components or cases.

Conclude with `absurd h' two_ne_zero`. Conclude with `absurd h' hd`. Conclude with `(Nat.cast_injective (sub_eq_zero.mp h)).symm`. Introduce `n`. Express the relevant statement in the definitionally equal form `((n : E) + (x - c x)) / ((n : E) - (x - c x)) * c (((n : E) + (x - c x)) / ((n : E) - (x - c x))) = 1`.

Rewrite using `[map_div₀, map_add, map_sub c (n : E) (x - c x), hcn, hcd]`. Establish `h4 : (n : E) + -(x - c x) = (n : E) - (x - c x)` using `by ring`. Establish `h5 : (n : E) - -(x - c x) = (n : E) + (x - c x)` using `by ring`. Rewrite using `[h4, h5, div_mul_div_comm, mul_comm ((n : E) - (x - c x))]`. Conclude with `div_self (mul_ne_zero (hadd n) (hsub n))`.
-/
theorem normOne_infinite {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (c : Gal(E/F)) (hc : ∀ x : E, (c : E → E) ((c : E → E) x) = x) (h1 : c ≠ (1 : Gal(E/F))) :
    Set.Infinite {l : E | l * (c : E → E) l = (1 : E)} := by
  have hx : ∃ x : E, c x ≠ x := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    exact h1 (AlgEquiv.ext fun x => by rw [hall x, AlgEquiv.one_apply])
  obtain ⟨x, hx⟩ := hx
  have hcd : c (x - c x) = -(x - c x) := by
    rw [map_sub, hc x]
    ring
  have hd : x - c x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcn : ∀ n : ℕ, c (n : E) = n := fun n => map_natCast c n
  have h2d : ∀ y : E, y = -y → y = 0 := by
    intro y hy
    have h2 : (2 : E) * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hsub : ∀ n : ℕ, (n : E) - (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = n := (sub_eq_zero.mp h0).symm
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, hcn]
      _ = -(x - c x) := hcd
  have hadd : ∀ n : ℕ, (n : E) + (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = -(n : E) := by linear_combination h0
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, map_neg, hcn]
      _ = -(x - c x) := hcd
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + (x - c x)) / ((n : E) - (x - c x))) ?_ ?_
  · intro n m hnm
    simp only at hnm
    rw [div_eq_div_iff (hsub n) (hsub m)] at hnm
    have h3 : (2 : E) * (x - c x) * ((m : E) - n) = 0 := by linear_combination hnm
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' two_ne_zero
      · exact absurd h' hd
    · exact (Nat.cast_injective (sub_eq_zero.mp h)).symm
  · intro n
    change ((n : E) + (x - c x)) / ((n : E) - (x - c x)) *
      c (((n : E) + (x - c x)) / ((n : E) - (x - c x))) = 1
    rw [map_div₀, map_add, map_sub c (n : E) (x - c x), hcn, hcd]
    have h4 : (n : E) + -(x - c x) = (n : E) - (x - c x) := by ring
    have h5 : (n : E) - -(x - c x) = (n : E) + (x - c x) := by ring
    rw [h4, h5, div_mul_div_comm, mul_comm ((n : E) - (x - c x))]
    exact div_self (mul_ne_zero (hadd n) (hsub n))

end GlobalTheory.NormOneInfinite
