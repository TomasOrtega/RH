import Mathlib

namespace GlobalTheory.ProofStatement

/- English proof (translation)
Introduce `l hl a ha`. Use `set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK`. Use `haveI : FiniteDimensional (ZMod l) K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)`. Use `haveI : Finite K := Module.finite_of_finite (ZMod l)`. Use `letI : Fintype K := Fintype.ofFinite K`.

Use `haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l`. Take `⟨n, _, hcard⟩` from `FiniteField.card K l`. Establish `ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0`. Introduce `h`. Apply `ha` to reduce the goal to its premises.

Conclude with `congrArg Subtype.val h`. Establish `hpow` using `FiniteField.pow_card_sub_one_eq_one _ ha'`. Establish `hl1 : 2 ≤ l` using `hl.out.two_le`. Establish `hn : 1 ≤ (n : ℕ)` using `n.pos`. Establish `hq : l ≤ l ^ (n : ℕ)` using `Nat.le_self_pow (by omega) l`.

Use `⟨Fintype.card K - 1, by omega, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcard]`. Introduce `hd`. Establish `h2 : l ∣ l ^ (n : ℕ)` using `dvd_pow_self l (by omega)`. Establish `h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1)` using `Nat.dvd_sub h2 hd`.

Rewrite `h3` using `[Nat.sub_sub_self (by omega)]`. Conclude with `hl.out.one_lt.ne' (Nat.dvd_one.mp h3)`. Use `congrArg Subtype.val hpow` as an intermediate fact. Simplify using `using this`.
-/
theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.ProofStatement
