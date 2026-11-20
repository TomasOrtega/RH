import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ComapDomainInlAdd

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

def Good (ε : Fin m → Bool) (d : ℕ) (r : Sym m n) : Prop := SymbolInFirstFamily ε r ∧ EtaLt r d

/- English proof (translation)
Apply the tactic sequence `constructor <;> intro t ht <;> simp at ht`.
-/
theorem good_zero (d : ℕ) : Good ε d (0 : Sym m n) := by
  constructor <;> intro t ht <;> simp at ht

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `t ht k hk`. Break down `Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h` into its components or cases. Conclude with `h₁.1 t h k hk`. Conclude with `h₂.1 t h k hk`.

Introduce `t ht`. Break down `Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h` into its components or cases. Conclude with `h₁.2 t h`. Conclude with `h₂.2 t h`.
-/
theorem good_add {d : ℕ} {r₁ r₂ : Sym m n} (h₁ : Good ε d r₁) (h₂ : Good ε d r₂) : Good ε d (r₁ + r₂) := by
  classical
  constructor
  · intro t ht k hk
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.1 t h k hk
    · exact h₂.1 t h k hk
  · intro t ht
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.2 t h
    · exact h₂.2 t h

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun t ht => h.1 t (MvPolynomial.support_smul ht), fun t ht => h.2 t (MvPolynomial.support_smul ht)⟩`.
-/
theorem good_smul {d : ℕ} {r : Sym m n} (a : ℂ) (h : Good ε d r) : Good ε d (a • r) :=
  ⟨fun t ht => h.1 t (MvPolynomial.support_smul ht), fun t ht => h.2 t (MvPolynomial.support_smul ht)⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using good_zero d`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `good_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem good_sum {ι : Type*} (S : Finset ι) {d : ℕ} (r : ι → Sym m n) (h : ∀ i ∈ S, Good ε d (r i)) :
    Good ε d (∑ i ∈ S, r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using good_zero d
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Rewrite `h` using `[MvPolynomial.mem_support_iff, coeff_mul_monomial']`. Use `split_ifs at h with hs`. Use `⟨t' - s, ?_, (tsub_add_cancel_of_le hs).symm⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`.

Rewrite `h` using `[h0, zero_mul]`. Conclude with `h rfl`. Conclude with `absurd rfl h`.
-/
theorem mem_support_mul_monomial {p : Sym m n} {s t' : Ix m n ⊕ Ix m n →₀ ℕ} {a : ℂ}
    (h : t' ∈ (p * monomial s a).support) : ∃ t ∈ p.support, t' = t + s := by
  rw [MvPolynomial.mem_support_iff, coeff_mul_monomial'] at h
  split_ifs at h with hs
  · refine ⟨t' - s, ?_, (tsub_add_cancel_of_le hs).symm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0; rw [h0, zero_mul] at h; exact h rfl
  · exact absurd rfl h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `t' ht' k hk`. Take `⟨t, ht, rfl⟩` from `mem_support_mul_monomial ht'`. Simplify using `only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk`. Distinguish the cases in `h1 : t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0`.

Conclude with `h.1 t ht k h1`. Use `push_neg at h1`. Apply `hs k` to reduce the goal to its premises. Break down `hk with hk | hk` into its components or cases. Break down `hk with hk | hk` into its components or cases.

Conclude with `absurd h1.1 hk`. Conclude with `Or.inl hk`. Break down `hk with hk | hk` into its components or cases. Conclude with `absurd h1.2 hk`. Conclude with `Or.inr hk`.

Introduce `t' ht'`. Take `⟨t, ht, rfl⟩` from `mem_support_mul_monomial ht'`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`. Conclude with `add_lt_add_of_lt_of_le (h.2 t ht) he`.
-/
theorem good_mul_monomial {d e : ℕ} {r : Sym m n} (h : Good ε d r) (s : Ix m n ⊕ Ix m n →₀ ℕ)
    (hs : ∀ k, (s (Sum.inl k) ≠ 0 ∨ s (Sum.inr k) ≠ 0) → inF1 ε k) (he : (∑ k, s (Sum.inr k)) ≤ e) :
    Good ε (d + e) (r * monomial s 1) := by
  constructor
  · intro t' ht' k hk
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0
    · exact h.1 t ht k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    exact add_lt_add_of_lt_of_le (h.2 t ht) he

/- English proof (translation)
Establish `hu : pderiv i u = ∑ t ∈ u.support, monomial (t - Finsupp.single i 1) (coeff t u * (t i : ℂ))` using `by conv_lhs => rw [u.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_monomial]`. Rewrite `h` using `[MvPolynomial.mem_support_iff, hu, coeff_sum]`.

Take `⟨t, ht, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Rewrite `hne` using `[coeff_monomial]`. Use `split_ifs at hne with heq`. Establish `hti : t i ≠ 0`. Introduce `h0`.

Rewrite `hne` using `[h0]`. Simplify using `at hne`. Use `⟨t, ht, hti, ?_⟩` and prove the remaining obligations. Rewrite using `[← heq, tsub_add_cancel_of_le]`. Rewrite using `[Finsupp.single_le_iff]`.

Use linear arithmetic over natural numbers and integers. Conclude with `absurd rfl hne`.
-/
theorem mem_support_pderiv {u : Sym m n} {i : Ix m n ⊕ Ix m n} {t' : Ix m n ⊕ Ix m n →₀ ℕ}
    (h : t' ∈ (pderiv i u).support) : ∃ t ∈ u.support, t i ≠ 0 ∧ t = t' + Finsupp.single i 1 := by
  classical
  have hu : pderiv i u = ∑ t ∈ u.support, monomial (t - Finsupp.single i 1) (coeff t u * (t i : ℂ)) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  rw [MvPolynomial.mem_support_iff, hu, coeff_sum] at h
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_monomial] at hne
  split_ifs at hne with heq
  · have hti : t i ≠ 0 := by
      intro h0; rw [h0] at hne; simp at hne
    refine ⟨t, ht, hti, ?_⟩
    rw [← heq, tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]; omega
  · exact absurd rfl hne

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `t' ht' j hj`. Take `⟨t, ht, -, rfl⟩` from `mem_support_pderiv ht'`. Apply `hu _ ht j` to reduce the goal to its premises. Simplify using `only [Finsupp.add_apply, ne_eq] at hj ⊢`.

Use linear arithmetic over natural numbers and integers. Introduce `t' ht'`. Take `⟨t, ht, hti, rfl⟩` from `mem_support_pderiv ht'`. Establish `h1` using `hue _ ht`. Establish `h3 : ∑ j, t' (Sum.inr j) + 1 ≤ d`.

Simplify `h1` using `[Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem good_pderiv {d : ℕ} {u : Sym m n} (hu : SymbolInFirstFamily ε u) (hue : EtaLe u d) (k : Ix m n) :
    Good ε d (pderiv (Sum.inr k) u) := by
  constructor
  · intro t' ht' j hj
    obtain ⟨t, ht, -, rfl⟩ := mem_support_pderiv ht'
    apply hu _ ht j
    simp only [Finsupp.add_apply, ne_eq] at hj ⊢
    omega
  · intro t' ht'
    obtain ⟨t, ht, hti, rfl⟩ := mem_support_pderiv ht'
    have h1 := hue _ ht
    have h3 : ∑ j, t' (Sum.inr j) + 1 ≤ d := by
      simpa [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply] using h1
    omega

/- English proof (translation)
Introduce `t ht` and use `(h.2 t ht).le`.
-/
theorem good_le {d : ℕ} {r : Sym m n} (h : Good ε d r) : EtaLe r d := fun t ht => (h.2 t ht).le

/- English proof (translation)
Establish `hs : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨ (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k`. Introduce `k hk`. Simplify using `only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk`. Use `split_ifs at hk with h`. Substitute `h` using the available equality.

Conclude with `ha`. Conclude with `absurd rfl hk`. Establish `h0 : (∑ k, (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ 0`. Simplify using `[Finsupp.single_apply]`. Rewrite using `[X_pow_eq_monomial]`.

Use `⟨?_, fun d hd => ?_⟩` and prove the remaining obligations. Introduce `t ht k hk`. Take `⟨t0, ht0, rfl⟩` from `mem_support_mul_monomial ht`. Simplify using `only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk`. Distinguish the cases in `h1 : t0 (Sum.inl k) ≠ 0 ∨ t0 (Sum.inr k) ≠ 0`.

Conclude with `hu t0 ht0 k h1`. Use `push_neg at h1`. Apply `hs k` to reduce the goal to its premises. Break down `hk with hk | hk` into its components or cases. Break down `hk with hk | hk` into its components or cases.

Conclude with `absurd h1.1 hk`. Conclude with `Or.inl hk`. Break down `hk with hk | hk` into its components or cases. Conclude with `absurd h1.2 hk`. Conclude with `Or.inr hk`.

Introduce `t ht`. Take `⟨t0, ht0, rfl⟩` from `mem_support_mul_monomial ht`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem first_family_symbol_mul_variable_pow {u : Sym m n} (hu : SymbolInFirstFamily ε u) {a : Ix m n} (ha : inF1 ε a) (b : ℕ) :
    SymbolInFirstFamily ε (u * X (Sum.inl a) ^ b) ∧ ∀ d, EtaLe u d → EtaLe (u * X (Sum.inl a) ^ b) d := by
  have hs : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
      (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
    intro k hk
    simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
    split_ifs at hk with h
    · subst h; exact ha
    · exact absurd rfl hk
  have h0 : (∑ k, (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ 0 := by
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial]
  refine ⟨?_, fun d hd => ?_⟩
  · intro t ht k hk
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t0 (Sum.inl k) ≠ 0 ∨ t0 (Sum.inr k) ≠ 0
    · exact hu t0 ht0 k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    calc _ ≤ d + 0 := add_le_add (hd t0 ht0) h0
      _ = d := add_zero d

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
