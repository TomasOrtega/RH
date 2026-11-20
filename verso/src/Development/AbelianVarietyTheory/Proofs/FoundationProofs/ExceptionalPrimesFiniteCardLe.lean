import Mathlib
import Formalism.CyclotomicNorms.StatementI

open Finset

namespace GlobalTheory

/- English proof (translation)
Use `set F : Finset ℕ := n.primeFactors.filter (fun ℓ => m < ℓ ^ (4 * padicValNat ℓ n)) with hF`. Establish `hS : {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} = (F : Set ℕ)`. Use extensionality with `ℓ`. Simplify using `only [hF, Set.mem_ofPred_eq, coe_filter, Nat.mem_primeFactors]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hp, h⟩`. Use `⟨⟨hp, ?_, hn⟩, h⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hd`. Rewrite `h` using `[padicValNat.eq_zero_of_not_dvd hd]`. Simplify using `at h`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨⟨hp, -, -⟩, h⟩`. Conclude with `⟨hp, h⟩`. Rewrite using `[hS]`. Use `⟨F.finite_toSet, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.ncard_coe_finset]`. Assume the negation of the conclusion as `hc`. Establish `hc4 : 4 ≤ F.card` using `by omega`. Establish `h1 : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ≤ n`. Establish `e : ∏ ℓ ∈ n.primeFactors, ℓ ^ padicValNat ℓ n = n` using `by conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]`.

Rewrite using `[Finsupp.prod, Nat.support_factorization]`. Use `Finset.prod_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]`. Establish `hd : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ∣ n` using `by conv_rhs => rw [← e]`. Conclude with `Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)`.

Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd`. Establish `h2 : m ^ F.card ≤ ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n)` using `Finset.pow_card_le_prod F _ m fun ℓ hℓ => ((Finset.mem_filter.1 hℓ).2).le`. Establish `h3 : ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4`. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_mul, mul_comm]`. Establish `h4 : m ^ 4 ≤ m ^ F.card` using `Nat.pow_le_pow_right (by omega) hc4`. Establish `h5 : (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 ≤ n ^ 4` using `Nat.pow_le_pow_left h1 4`. Establish `h6 : n ^ 4 < m ^ 4` using `Nat.pow_lt_pow_left hm (by norm_num)`. Use linear arithmetic over natural numbers and integers.
-/
theorem exceptional_primes_finite_card_le (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    Set.Finite {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ∧
      Set.ncard {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ≤ 3 := by
  classical
  set F : Finset ℕ := n.primeFactors.filter (fun ℓ => m < ℓ ^ (4 * padicValNat ℓ n)) with hF
  have hS : {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} = (F : Set ℕ) := by
    ext ℓ
    simp only [hF, Set.mem_ofPred_eq, coe_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨⟨hp, ?_, hn⟩, h⟩
      by_contra hd
      rw [padicValNat.eq_zero_of_not_dvd hd] at h
      simp at h
      omega
    · rintro ⟨⟨hp, -, -⟩, h⟩
      exact ⟨hp, h⟩
  rw [hS]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  by_contra hc
  have hc4 : 4 ≤ F.card := by omega
  have h1 : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ≤ n := by
    have e : ∏ ℓ ∈ n.primeFactors, ℓ ^ padicValNat ℓ n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
    have hd : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ∣ n := by
      conv_rhs => rw [← e]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h2 : m ^ F.card ≤ ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) :=
    Finset.pow_card_le_prod F _ m fun ℓ hℓ => ((Finset.mem_filter.1 hℓ).2).le
  have h3 : ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have h4 : m ^ 4 ≤ m ^ F.card := Nat.pow_le_pow_right (by omega) hc4
  have h5 : (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left h1 4
  have h6 : n ^ 4 < m ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
  omega

/- English proof (translation)
Introduce `g hg`. Establish `key : ∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ∧ Set.ncard {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ≤ 3`. Introduce `d hd`. Establish `h1 : 1 < g ^ d` using `Nat.one_lt_pow (by omega) (by omega)`. Conclude with `exceptional_primes_finite_card_le (g ^ d - 1) (g ^ d) (by omega) (by omega)`.

Use `⟨key, fun N => ?_⟩` and prove the remaining obligations. Proceed by induction on `N with`. Consider the case `zero`. Establish `: Formalism.CyclotomicNorms.BB 0 g = {g}`. Use extensionality with `ℓ`.

Simplify using `only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | ⟨d, h1, h2, -⟩)`. Conclude with `h`. Use linear arithmetic over natural numbers and integers.

Conclude with `Or.inl`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ N ih`. Establish `: Formalism.CyclotomicNorms.BB (N + 1) g = Formalism.CyclotomicNorms.BB N g ∪ {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}`.

Use extensionality with `ℓ`. Simplify using `only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | ⟨d, h1, h2, h3⟩)`. Conclude with `Or.inl (Or.inl h)`.

Break down `Nat.lt_or_ge N d with h | h` into its components or cases. Take `rfl : d = N + 1` from `by omega`. Conclude with `Or.inr h3`. Conclude with `Or.inl (Or.inr ⟨d, h1, h, h3⟩)`. Introduce and unpack `((h | ⟨d, h1, h2, h3⟩) | h)`.

Conclude with `Or.inl h`. Conclude with `Or.inr ⟨d, h1, by omega, h3⟩`. Conclude with `Or.inr ⟨N + 1, by omega, le_rfl, h⟩`. Rewrite using `[this]`. Take `⟨hf, hc⟩` from `key (N + 1) (by omega)`.

Use `⟨ih.1.union hf, ?_⟩` and prove the remaining obligations. Use `Set.ncard_union_le (Formalism.CyclotomicNorms.BB N g) {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}` as an intermediate fact. Use `ih.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exceptional_set_count : Formalism.CyclotomicNorms.BBCount := by
  intro g hg
  have key : ∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ∧
      Set.ncard {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ≤ 3 := by
    intro d hd
    have h1 : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    exact exceptional_primes_finite_card_le (g ^ d - 1) (g ^ d) (by omega) (by omega)
  refine ⟨key, fun N => ?_⟩
  induction N with
  | zero =>
    have : Formalism.CyclotomicNorms.BB 0 g = {g} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, -⟩)
        · exact h
        · omega
      · exact Or.inl
    rw [this]
    simp
  | succ N ih =>
    have : Formalism.CyclotomicNorms.BB (N + 1) g = Formalism.CyclotomicNorms.BB N g ∪ {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge N d with h | h
          · obtain rfl : d = N + 1 := by omega
            exact Or.inr h3
          · exact Or.inl (Or.inr ⟨d, h1, h, h3⟩)
      · rintro ((h | ⟨d, h1, h2, h3⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨d, h1, by omega, h3⟩
        · exact Or.inr ⟨N + 1, by omega, le_rfl, h⟩
    rw [this]
    obtain ⟨hf, hc⟩ := key (N + 1) (by omega)
    refine ⟨ih.1.union hf, ?_⟩
    have := Set.ncard_union_le (Formalism.CyclotomicNorms.BB N g) {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}
    have := ih.2
    omega

end GlobalTheory
