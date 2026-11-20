import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

/- English proof (translation)
Introduce `b j M e`. Establish `h2 : ∀ n : ℕ, ∃ w : ℤ, (b + M * j) ^ n = b ^ n + M * w`. Introduce `n`. Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow (b + M * j) b n`. Use `⟨j * c, ?_⟩` and prove the remaining obligations.

Establish `hd : (b + M * j) - b = M * j` using `by ring`. Rewrite `hc` using `[hd]`. Take the linear combination `hc`. Use `⟨?_, h2 e⟩` and prove the remaining obligations. Proceed by induction on `e with`.

Consider the case `zero => exact ⟨0, by ring⟩`. Consider the case `succ n ih`. Take `⟨z, hz⟩` from `ih`. Use `⟨b * z + ((n : ℤ) + 1) * b ^ n * j ^ 2 + M * j * z, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `(b + M * j) * hz`.
-/
theorem UpperTheory.V.Stk.exists_binomial_expansion_mod_sq :
    ∀ (b j M : ℤ) (e : ℕ),
      (∃ z : ℤ, (b + M * j) ^ (e + 1) = b ^ (e + 1) + ((e : ℤ) + 1) * b ^ e * (M * j) + M ^ 2 * z) ∧
      ∃ w : ℤ, (b + M * j) ^ e = b ^ e + M * w := by
  intro b j M e
  have h2 : ∀ n : ℕ, ∃ w : ℤ, (b + M * j) ^ n = b ^ n + M * w := by
    intro n
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (b + M * j) b n
    refine ⟨j * c, ?_⟩
    have hd : (b + M * j) - b = M * j := by ring
    rw [hd] at hc
    linear_combination hc
  refine ⟨?_, h2 e⟩
  induction e with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨b * z + ((n : ℤ) + 1) * b ^ n * j ^ 2 + M * j * z, ?_⟩
    push_cast
    linear_combination (b + M * j) * hz
