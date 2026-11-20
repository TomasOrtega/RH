import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleTypeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardCycleTypeConsMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

/- English proof (translation)
Take `⟨t, rfl⟩` from `Multiset.exists_cons_of_mem hp`. Establish `hq' : q ∈ t` using `(Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)`. Take `⟨u, rfl⟩` from `Multiset.exists_cons_of_mem hq'`. Rewrite using `[Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]`. Conclude with `Nat.le_add_right _ _`.
-/
theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) (h : p ≠ q) : p + q ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  have hq' : q ∈ t := (Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hq'
  rw [Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]
  exact Nat.le_add_right _ _

/- English proof (translation)
Establish `hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N` using `fun σ => by`. Simplify using `using σ.partition.parts_sum`. Establish `hdisj : (S : Set ℕ).PairwiseDisjoint fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts`. Introduce `p hp q hq hpq`. Rewrite using `[Function.onFun, Finset.disjoint_filter]`.

Introduce `σ _ hpσ hqσ`. Establish `h1` using `add_le_sum_of_mem_of_ne hpσ hqσ hpq`. Rewrite `h1` using `[hsum σ]`. Establish `h2` using `hS p hp`. Establish `h3` using `hS q hq`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.card_biUnion hdisj]`. Establish `hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) = (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ`. Use extensionality with `σ`. Simplify using the standard rewrite rules.

Rewrite using `[hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]`.
-/
theorem card_perm_no_long_cycle (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]

/- English proof (translation)
Introduce `g _ N hN`. Use `set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef`. Establish `hS : ∀ p ∈ S, N < 2 * p` using `fun p hp => (Finset.mem_filter.mp hp).2.2.1`. Establish `hSN : ∀ p ∈ S, p ≤ N` using `fun p hp => Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)`. Establish `hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ mass g N fun f => ∀ p ∈ S, p ∉ degType g f`.

Establish `hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆ (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f)`. Introduce `f hf`. Rewrite `hf`, the goal using `[Finset.mem_filter]`. Use `⟨hf.1, ?_⟩` and prove the remaining obligations. Introduce `p hp hpf`.

Apply `hf.2` to reduce the goal to its premises. Unfold `degType at hpf`. Unfold `HasPrimeFactor`. Take `⟨h, hh, rfl⟩` from `Multiset.mem_map.mp hpf`. Take `⟨-, hpr, h2, h3⟩` from `Finset.mem_filter.mp hp`.

Conclude with `⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩`. Unfold `mass`. Use `Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub (fun f _ _ => by positivity)` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Establish `hT` using `GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)`.

Establish `hcount` using `card_perm_no_long_cycle N S hS`. Establish `hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card : ℝ) = N.factorial / p`. Introduce `p hp`. Establish `hp0 : 0 < p` using `by have := hS p hp; omega`. Establish `hp0' : (p : ℝ) ≠ 0` using `by exact_mod_cast hp0.ne'`.

Rewrite using `[eq_div_iff hp0']`. Conclude with `card_perm_long_cycle N p (hS p hp) (hSN p hp)` after adjusting the coercions. Establish `hfac : (N.factorial : ℝ) ≠ 0` using `by positivity`. Establish `hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p`. Establish `hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p`.

Rewrite using `[← Finset.sum_congr rfl hlong]`. Use `congrArg (fun n : ℕ => (n : ℝ)) hcount` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hc, sub_div, div_self hfac, Finset.sum_div]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[div_right_comm, div_self hfac]`. Establish `hprimes` using `inv_log_le_sum_inv_primes_between N hN`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mass_not_hasPrimeFactor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
    rfl
  have hT := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith

end GlobalTheory.BadShare
