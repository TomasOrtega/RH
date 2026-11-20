import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `n p t a c hmono hpt hpt' hn hrun hleft hright hwin`. Take `⟨j0, hj0n, hj0⟩` from `hwin 0 (by omega)`. Establish `key : ∀ i, i < t → j0 + i < n ∧ a (j0 + i) = a j0`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro _`. Simplify using `using hj0n`. Consider the case `succ i ih`. Introduce `hi`. Take `⟨h1, h2⟩` from `ih (by omega)`.

Take `⟨j, hjn, hj⟩` from `hwin (i + 1) hi`. Move the coercions through the operations in `at hj hj0`. Establish `hge : j0 + i + 1 ≤ j`. Assume the negation of the conclusion as `hlt`. Use `hmono j (j0 + i) (by omega) h1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hle` using `hmono (j0 + i) j (by omega) hjn`. Establish `hj' : j = j0 + i + 1` using `by omega`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[show j0 + (i + 1) = j by omega]`.

Use linear arithmetic over natural numbers and integers. Establish `hq` using `(key (t - 1) (by omega)).1`. Establish `hconst : ∀ k, j0 ≤ k → k < j0 + t → a k = a j0`. Introduce `k h1 h2`. Use `(key (k - j0) (by omega)).2` as an intermediate fact.

Rewrite `this` using `[show j0 + (k - j0) = k by omega]`. Then use the resulting hypothesis. Break down `lt_trichotomy j0 p with h | h | h` into its components or cases. It suffices to derive a contradiction. Establish `e1` using `hconst (p - 1) (by omega) (by omega)`. Establish `e2` using `hconst p (by omega) (by omega)`.

Use `hleft (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Substitute `h` using the available equality. Move the coercions through the operations in `at hj0`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Establish `e1` using `hconst (p + t - 1) (by omega) (by omega)`. Establish `e2` using `hconst (p + t) (by omega) (by omega)`. Establish `e3` using `hrun (p + t - 1) (by omega) (by omega)`. Use `hright (by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem block_is_the_run : ∀ (n p t : ℕ) (a : ℕ → ℤ) (c : ℤ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    p + t ≤ n → p < t → n - (p + t) < t → (∀ j, p ≤ j → j < p + t → a j = a p) →
    (1 ≤ p → a p < a (p - 1)) → (p + t < n → a (p + t) < a p) →
    (∀ i < t, ∃ j < n, a j - j = c - i) → c = a p - p := by
  intro n p t a c hmono hpt hpt' hn hrun hleft hright hwin
  obtain ⟨j0, hj0n, hj0⟩ := hwin 0 (by omega)

  have key : ∀ i, i < t → j0 + i < n ∧ a (j0 + i) = a j0 := by
    intro i
    induction i with
    | zero => intro _; simpa using hj0n
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨j, hjn, hj⟩ := hwin (i + 1) hi
      push_cast at hj hj0
      have hge : j0 + i + 1 ≤ j := by
        by_contra hlt
        have := hmono j (j0 + i) (by omega) h1
        omega
      have hle := hmono (j0 + i) j (by omega) hjn
      have hj' : j = j0 + i + 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [show j0 + (i + 1) = j by omega]
      omega
  have hq := (key (t - 1) (by omega)).1
  have hconst : ∀ k, j0 ≤ k → k < j0 + t → a k = a j0 := by
    intro k h1 h2
    have := (key (k - j0) (by omega)).2
    rwa [show j0 + (k - j0) = k by omega] at this
  rcases lt_trichotomy j0 p with h | h | h
  ·
    exfalso
    have e1 := hconst (p - 1) (by omega) (by omega)
    have e2 := hconst p (by omega) (by omega)
    have := hleft (by omega)
    omega
  · subst h
    push_cast at hj0
    omega
  ·
    exfalso
    have e1 := hconst (p + t - 1) (by omega) (by omega)
    have e2 := hconst (p + t) (by omega) (by omega)
    have e3 := hrun (p + t - 1) (by omega) (by omega)
    have := hright (by omega)
    omega

end GlobalTheory
