import Mathlib

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

/- English proof (translation)
Rewrite using `[Nat.factorial_succ, padicValNat.mul (Nat.add_one_ne_zero M) (Nat.factorial_ne_zero M)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValNat_factorial_succ (p : ℕ) [Fact p.Prime] (M : ℕ) :
    padicValNat p (M + 1).factorial = padicValNat p M.factorial + padicValNat p (M + 1) := by
  rw [Nat.factorial_succ, padicValNat.mul (Nat.add_one_ne_zero M) (Nat.factorial_ne_zero M)]
  omega

/- English proof (translation)
Proceed by induction on `M, h using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ M hKM ih`. Rewrite using `[Finset.sum_Ioc_succ_top hKM, padicValNat_factorial_succ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValNat_sum_Ioc_add_factorial (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    ∑ k ∈ Finset.Ioc K M, padicValNat p k + padicValNat p K.factorial = padicValNat p M.factorial := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ioc_succ_top hKM, padicValNat_factorial_succ]
    omega

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `h1 : (p.digits K).sum ≤ (p.digits K).length * (p - 1)`. Use `List.sum_le_card_nsmul (p.digits K) (p - 1) (fun x hx => by` as an intermediate fact. Use `Nat.digits_lt_base hp.one_lt hx` as an intermediate fact. Use the proof step `omega)`.

Simplify using `using this`. Establish `h2 : (p.digits K).length ≤ Nat.log p K + 1`. Break down `Nat.eq_zero_or_pos K with rfl | hK` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Nat.digits_len p K hp.one_lt hK.ne']`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem digits_sum_le_log (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (p.digits K).sum ≤ (p - 1) * (Nat.log p K + 1) := by
  have hp : p.Prime := Fact.out
  have h1 : (p.digits K).sum ≤ (p.digits K).length * (p - 1) := by
    have := List.sum_le_card_nsmul (p.digits K) (p - 1) (fun x hx => by
      have := Nat.digits_lt_base hp.one_lt hx
      omega)
    simpa using this
  have h2 : (p.digits K).length ≤ Nat.log p K + 1 := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [Nat.digits_len p K hp.one_lt hK.ne']
  calc (p.digits K).sum ≤ (p.digits K).length * (p - 1) := h1
    _ ≤ (Nat.log p K + 1) * (p - 1) := Nat.mul_le_mul h2 (le_refl _)
    _ = (p - 1) * (Nat.log p K + 1) := Nat.mul_comm _ _

/- English proof (translation)
Establish `h2` using `padicValNat_sum_Ioc_add_factorial p K M h`. Establish `hM` using `sub_one_mul_padicValNat_factorial (p := p) M`. Establish `hK` using `sub_one_mul_padicValNat_factorial (p := p) K`. Establish `sM` using `Nat.digit_sum_le p M`. Establish `sK` using `Nat.digit_sum_le p K`.

Establish `e : (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k + (p - 1) * padicValNat p K.factorial = (p - 1) * padicValNat p M.factorial`. Rewrite using `[← Nat.mul_add, h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValNat_sum_Ioc_le (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k ≤ M - K + (p.digits K).sum := by
  have h2 := padicValNat_sum_Ioc_add_factorial p K M h
  have hM := sub_one_mul_padicValNat_factorial (p := p) M
  have hK := sub_one_mul_padicValNat_factorial (p := p) K
  have sM := Nat.digit_sum_le p M
  have sK := Nat.digit_sum_le p K
  have e : (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k + (p - 1) * padicValNat p K.factorial =
      (p - 1) * padicValNat p M.factorial := by
    rw [← Nat.mul_add, h2]
  omega

/- English proof (translation)
Establish `e : ∑ k ∈ Y.image Int.natAbs, padicValNat p k = ∑ x ∈ Y, padicValInt p x` using `Finset.sum_image (by intro x hx y hy hxy; exact hinj x hx y hy hxy)`. Rewrite using `[← e]`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_image]`.

Take `⟨x, hx, rfl⟩` from `hk`. Rewrite using `[Finset.mem_Ioc]`. Conclude with `hY x hx`.
-/
theorem padicValInt_sum_le_Ioc (p : ℕ) (Y : Finset ℤ) (K M : ℕ) (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    ∑ x ∈ Y, padicValInt p x ≤ ∑ k ∈ Finset.Ioc K M, padicValNat p k := by
  have e : ∑ k ∈ Y.image Int.natAbs, padicValNat p k = ∑ x ∈ Y, padicValInt p x :=
    Finset.sum_image (by intro x hx y hy hxy; exact hinj x hx y hy hxy)
  rw [← e]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  rw [Finset.mem_Ioc]
  exact hY x hx

/- English proof (translation)
The claim follows from `le_trans (Nat.mul_le_mul (le_refl _) (padicValInt_sum_le_Ioc p Y K M hY hinj)) (padicValNat_sum_Ioc_le p K M h)`.
-/
private theorem sub_one_mul_sum_padicValInt_le_sub_add_digits_sum (p : ℕ) [Fact p.Prime] (Y : Finset ℤ) (K M : ℕ) (h : K ≤ M)
    (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    (p - 1) * ∑ x ∈ Y, padicValInt p x ≤ M - K + (p.digits K).sum :=
  le_trans (Nat.mul_le_mul (le_refl _) (padicValInt_sum_le_Ioc p Y K M hY hinj))
    (padicValNat_sum_Ioc_le p K M h)

/- English proof (translation)
Establish `e1 : ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x + ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x = ∑ x ∈ X, padicValInt p x` using `Finset.sum_filter_add_sum_filter_not X (fun x => x ≤ (a : ℤ) - bb) (padicValInt p)`. Establish `e2 : ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x + ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x), padicValInt p x = ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x` using `Finset.sum_filter_add_sum_filter_not _ (fun x => 0 < x) (padicValInt p)`. Establish `b1 : (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x ≤ (bb + S - 1) - (bb - a - 1) + (p.digits (bb - a - 1)).sum`. Apply `sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)` to reduce the goal to its premises. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_filter]`. Establish `hx'` using `hX x hx.1`. Move the coercions through the operations in `at hx'`. Apply the tactic sequence `rcases Int.natAbs_eq x with h | h <;> omega`. Introduce `x hx y hy hxy`.

Rewrite `hx`, `hy` using `[Finset.mem_filter]`. Apply the tactic sequence `rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega`. Establish `b2 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x ≤ (η + a) - 0 + (p.digits 0).sum`. Apply `sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)` to reduce the goal to its premises. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_filter, Finset.mem_filter]`. Establish `hx'` using `hX x hx.1.1`. Move the coercions through the operations in `at hx'`. Apply the tactic sequence `rcases Int.natAbs_eq x with h | h <;> omega`. Introduce `x hx y hy hxy`.

Rewrite `hx`, `hy` using `[Finset.mem_filter, Finset.mem_filter]`. Apply the tactic sequence `rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega`. Establish `b3 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x), padicValInt p x ≤ η - 0 + (p.digits 0).sum`. Apply `sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)` to reduce the goal to its premises. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_filter, Finset.mem_filter]`. Establish `hx'` using `hX x hx.1.1`. Move the coercions through the operations in `at hx'`. Apply the tactic sequence `rcases Int.natAbs_eq x with h | h <;> omega`. Introduce `x hx y hy hxy`.

Rewrite `hx`, `hy` using `[Finset.mem_filter, Finset.mem_filter]`. Establish `hx'` using `hX x hx.1.1`. Establish `hy'` using `hX y hy.1.1`. Apply the tactic sequence `rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega`. Establish `z : (p.digits 0).sum = 0` using `by simp`.

Establish `d` using `digits_sum_le_log p (bb - a - 1)`. Establish `total : (p - 1) * ∑ x ∈ X, padicValInt p x = (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x + (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x + (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter …`. Rewrite using `[← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValInt_sum_le (p : ℕ) [Fact p.Prime] (bb S η a : ℕ) (hab : a + η < bb) (X : Finset ℤ)
    (hX : ∀ x ∈ X, x ≠ 0 ∧ ((1 - ((bb + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - bb) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ)))) :
    (p - 1) * ∑ x ∈ X, padicValInt p x ≤
      2 * a + 2 * η + S + (p - 1) * (Nat.log p (bb - a - 1) + 1) := by
  have e1 : ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x = ∑ x ∈ X, padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not X (fun x => x ≤ (a : ℤ) - bb) (padicValInt p)
  have e2 : ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x), padicValInt p x =
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not _ (fun x => 0 < x) (padicValInt p)
  have b1 : (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x ≤
      (bb + S - 1) - (bb - a - 1) + (p.digits (bb - a - 1)).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hx' := hX x hx.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b2 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x),
      padicValInt p x ≤ (η + a) - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b3 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
      padicValInt p x ≤ η - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      have hx' := hX x hx.1.1
      have hy' := hX y hy.1.1
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have z : (p.digits 0).sum = 0 := by simp
  have d := digits_sum_le_log p (bb - a - 1)
  have total : (p - 1) * ∑ x ∈ X, padicValInt p x =
      (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
        padicValInt p x := by
    rw [← e1, ← e2]
    ring
  omega

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
