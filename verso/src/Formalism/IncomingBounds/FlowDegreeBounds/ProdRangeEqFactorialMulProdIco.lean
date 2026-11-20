import Formalism.IncomingBounds.LemmaMNumerics

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

/- English proof (translation)
Introduce `l hl n n' hdvd`. Take `⟨m, hm⟩` from `hdvd`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : (l : ℝ) - 1 ≠ 0` using `(by linarith : (0 : ℝ) < l - 1).ne'`.

Establish `h3 : (l : ℝ) + 1 ≠ 0` using `(by linarith : (0 : ℝ) < l + 1).ne'`. Establish `hmR : (n : ℝ) - l * n' = ((l : ℝ) ^ 2 - 1) * m` using `by exact_mod_cast hm`. Establish `hn : (n : ℝ) = ((l : ℝ) - 1) * ((l : ℝ) + 1) * m + l * n'` using `by linear_combination hmR`. Unfold `rho`. Rewrite using `[hn, show (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) by ring]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqSubOneInvMulDvd : InvWeight := by
  intro l hl n n' hdvd
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < l - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < l + 1).ne'
  have hmR : (n : ℝ) - l * n' = ((l : ℝ) ^ 2 - 1) * m := by exact_mod_cast hm
  have hn : (n : ℝ) = ((l : ℝ) - 1) * ((l : ℝ) + 1) * m + l * n' := by linear_combination hmR
  unfold rho
  rw [hn, show (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) by ring]
  field_simp
  ring

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Proceed by induction on `v with`. Consider the case `zero => simp <;> exact Nat.ModEq.refl _`. Consider the case `succ v ih`. Rewrite using `[show l ^ (v + 1) * m = l * (l ^ v * m) by ring, show l ^ (v + 1) = l * l ^ v by ring]`.

Use `Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_` and prove the remaining obligations. Simplify using `only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl, Nat.choose_self, one_mul]`. Conclude with `ih`.
-/
private lemma binomGcd_lucas_lemma (l : ℕ) [Fact l.Prime] (m v : ℕ) :
    (l ^ v * m).choose (l ^ v) ≡ m [MOD l] := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  induction v with
  | zero => simp <;> exact Nat.ModEq.refl _
  | succ v ih =>
    rw [show l ^ (v + 1) * m = l * (l ^ v * m) by ring, show l ^ (v + 1) = l * l ^ v by ring]
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl, Nat.choose_self, one_mul]
    exact ih

/- English proof (translation)
Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hl0 : 0 < l` using `by omega`. Establish `hlt : l - 1 < l` using `by omega`. Proceed by induction on `a with`. Consider the case `zero => simp <;> exact Nat.ModEq.refl _`.

Consider the case `succ a ih`. Establish `e1 : 1 ≤ l ^ a` using `Nat.one_le_pow _ _ hl0`. Establish `e2 : 1 ≤ l ^ (a + 1)` using `Nat.one_le_pow _ _ hl0`. Establish `e3 : 1 ≤ l ^ (a + 1 + 1)` using `Nat.one_le_pow _ _ hl0`. Establish `hn : l ^ (a + 1 + 1) - 1 = (l - 1) + l * (l ^ (a + 1) - 1)` using `by zify [e2, e3, (by omega : 1 ≤ l)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hk : l ^ (a + 1) - 1 = (l - 1) + l * (l ^ a - 1)` using `by zify [e1, e2, (by omega : 1 ≤ l)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnk : (l ^ (a + 1 + 1) - 1).choose (l ^ (a + 1) - 1) = ((l - 1) + l * (l ^ (a + 1) - 1)).choose ((l - 1) + l * (l ^ a - 1))`. Rewrite using `[← hk, ← hn]`.

Rewrite using `[hnk]`. Use `Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_` and prove the remaining obligations. Simplify using `only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hl0, Nat.div_eq_of_lt hlt, zero_add, Nat.choose_self, one_mul]`. Conclude with `ih`.
-/
private lemma binomGcd_lucas_lemma_2 (l : ℕ) [Fact l.Prime] (a : ℕ) :
    (l ^ (a + 1) - 1).choose (l ^ a - 1) ≡ 1 [MOD l] := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : 0 < l := by omega
  have hlt : l - 1 < l := by omega
  induction a with
  | zero => simp <;> exact Nat.ModEq.refl _
  | succ a ih =>
    have e1 : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl0
    have e2 : 1 ≤ l ^ (a + 1) := Nat.one_le_pow _ _ hl0
    have e3 : 1 ≤ l ^ (a + 1 + 1) := Nat.one_le_pow _ _ hl0
    have hn : l ^ (a + 1 + 1) - 1 = (l - 1) + l * (l ^ (a + 1) - 1) := by
      zify [e2, e3, (by omega : 1 ≤ l)]
      ring
    have hk : l ^ (a + 1) - 1 = (l - 1) + l * (l ^ a - 1) := by
      zify [e1, e2, (by omega : 1 ≤ l)]
      ring
    have hnk : (l ^ (a + 1 + 1) - 1).choose (l ^ (a + 1) - 1) =
        ((l - 1) + l * (l ^ (a + 1) - 1)).choose ((l - 1) + l * (l ^ a - 1)) := by
      rw [← hk, ← hn]
    rw [hnk]
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hl0,
      Nat.div_eq_of_lt hlt, zero_add, Nat.choose_self, one_mul]
    exact ih

/- English proof (translation)
Introduce `l hl n hn`. Use `haveI := Fact.mk hl`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨k, hk0, hkn, hndvd⟩ ⟨e, rfl⟩`. Conclude with `hndvd (hl.dvd_choose_pow (by omega) (by omega))`.

Introduce `hnp`. Establish `hd1 : l ^ padicValNat l n ∣ n` using `pow_padicValNat_dvd`. Establish `hd2 : ¬ l ^ (padicValNat l n + 1) ∣ n` using `pow_succ_padicValNat_not_dvd (by omega)`. Generalize the expression as in `padicValNat l n = v at hd1 hd2`. Take `⟨m, rfl⟩` from `hd1`.

Establish `hlm : ¬ l ∣ m`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `hd2 ⟨c, by ring⟩`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hn` using `[mul_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hm1 : m ≠ 1` using `fun h => hnp ⟨v, by rw [h, mul_one]⟩`. Establish `hp : 0 < l ^ v` using `pow_pos hl.pos v`. Use `⟨l ^ v, hp, lt_mul_of_one_lt_right hp (by omega), ?_⟩` and prove the remaining obligations.

Introduce `hd`. Apply `hlm` to reduce the goal to its premises. Conclude with `Nat.modEq_zero_iff_dvd.1 ((binomGcd_lucas_lemma l m v).symm.trans (Nat.modEq_zero_iff_dvd.2 hd))`. Introduce `e he hne`. Substitute `hne` using the available equality.

Take `⟨a, rfl⟩ : ∃ a, e = a + 1` from `⟨e - 1, by omega⟩`. Use `⟨l ^ a, pow_pos hl.pos a, Nat.pow_lt_pow_right hl.one_lt (by omega), ?_⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ l ^ a` using `Nat.one_le_pow _ _ hl.pos`. Establish `h2 : 1 ≤ l ^ (a + 1)` using `Nat.one_le_pow _ _ hl.pos`. Establish `key` using `Nat.add_one_mul_choose_eq (l ^ (a + 1) - 1) (l ^ a - 1)`.

Simplify using `only [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at key`. Establish `hc : (l ^ (a + 1)).choose (l ^ a) = l * (l ^ (a + 1) - 1).choose (l ^ a - 1)`. Apply `Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos a)` to reduce the goal to its premises. Rewrite using `[← key, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `hdvd`. Rewrite `hdvd` using `[hc, pow_two, Nat.mul_dvd_mul_iff_left hl.pos]`. Establish `h3 : l ∣ 1` using `Nat.modEq_zero_iff_dvd.1 ((binomGcd_lucas_lemma_2 l a).symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.1 h3)`.
-/
theorem primeDvdChooseIff : BinomGcd := by
  intro l hl n hn
  haveI := Fact.mk hl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk0, hkn, hndvd⟩ ⟨e, rfl⟩
    exact hndvd (hl.dvd_choose_pow (by omega) (by omega))
  · intro hnp
    have hd1 : l ^ padicValNat l n ∣ n := pow_padicValNat_dvd
    have hd2 : ¬ l ^ (padicValNat l n + 1) ∣ n := pow_succ_padicValNat_not_dvd (by omega)
    generalize padicValNat l n = v at hd1 hd2
    obtain ⟨m, rfl⟩ := hd1
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      exact hd2 ⟨c, by ring⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hn
      omega
    have hm1 : m ≠ 1 := fun h => hnp ⟨v, by rw [h, mul_one]⟩
    have hp : 0 < l ^ v := pow_pos hl.pos v
    refine ⟨l ^ v, hp, lt_mul_of_one_lt_right hp (by omega), ?_⟩
    intro hd
    apply hlm
    exact Nat.modEq_zero_iff_dvd.1
      ((binomGcd_lucas_lemma l m v).symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
  · intro e he hne
    subst hne
    obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
    refine ⟨l ^ a, pow_pos hl.pos a, Nat.pow_lt_pow_right hl.one_lt (by omega), ?_⟩
    have h1 : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl.pos
    have h2 : 1 ≤ l ^ (a + 1) := Nat.one_le_pow _ _ hl.pos
    have key := Nat.add_one_mul_choose_eq (l ^ (a + 1) - 1) (l ^ a - 1)
    simp only [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at key
    have hc : (l ^ (a + 1)).choose (l ^ a) = l * (l ^ (a + 1) - 1).choose (l ^ a - 1) := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos a)
      rw [← key, pow_succ]
      ring
    intro hdvd
    rw [hc, pow_two, Nat.mul_dvd_mul_iff_left hl.pos] at hdvd
    have h3 : l ∣ 1 := Nat.modEq_zero_iff_dvd.1
      ((binomGcd_lucas_lemma_2 l a).symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))
    exact hl.one_lt.ne' (Nat.dvd_one.1 h3)

/- English proof (translation)
Introduce `l hl N hN`. Use `haveI := Fact.mk hl`. Establish `key` using `sub_one_mul_padicValNat_factorial (p := l) N`. Establish `hsN : (l.digits N).sum ≤ N` using `Nat.digit_sum_le l N`. Establish `hne : l.digits N ≠ []` using `Nat.digits_ne_nil_iff_ne_zero.2 (by omega)`.

Establish `hs1 : 1 ≤ (l.digits N).sum`. Establish `hpos : 0 < (l.digits N).getLast hne` using `Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero l (by omega))`. Use `List.le_sum_of_mem (List.getLast_mem hne)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hdig : (l.digits N).sum ≤ (Nat.log l N + 1) * (l - 1)`.

Establish `hlen` using `Nat.digits_len l N hl.one_lt (by omega)`. Use `List.sum_le_card_nsmul (l.digits N) (l - 1) (fun x hx => by have := Nat.digits_lt_base hl.one_lt hx; omega)` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, hlen]`. Then use the resulting hypothesis. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `hl1 : (0 : ℝ) < l - 1` using `by linarith`.

Establish `e` using `congrArg (fun t : ℕ => (t : ℝ)) key`. Simplify using `only [Nat.cast_mul, Nat.cast_sub hsN, Nat.cast_sub hl.one_le, Nat.cast_one] at e`. Establish `hs1R : (1 : ℝ) ≤ ((l.digits N).sum : ℝ)` using `by exact_mod_cast hs1`. Establish `hdigR` using `(Nat.cast_le (α := ℝ)).2 hdig`. Simplify using `only [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_add, Nat.cast_one] at hdigR`.

Establish `hlog : (Nat.log l N : ℝ) ≤ Real.logb l N` using `Real.natLog_le_logb N l`. Prove the components needed by the constructor for the conclusion. Establish `h : (N : ℝ) / ((l : ℝ) - 1) ≤ (padicValNat l N.factorial : ℝ) + ((Nat.log l N : ℝ) + 1)`. Rewrite using `[div_le_iff₀ hl1]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hl1]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem padicValFactorialBounds : FactValBounds := by
  intro l hl N hN
  haveI := Fact.mk hl
  have key := sub_one_mul_padicValNat_factorial (p := l) N
  have hsN : (l.digits N).sum ≤ N := Nat.digit_sum_le l N
  have hne : l.digits N ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hs1 : 1 ≤ (l.digits N).sum := by
    have hpos : 0 < (l.digits N).getLast hne :=
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero l (by omega))
    have := List.le_sum_of_mem (List.getLast_mem hne)
    omega
  have hdig : (l.digits N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
    have hlen := Nat.digits_len l N hl.one_lt (by omega)
    have := List.sum_le_card_nsmul (l.digits N) (l - 1)
      (fun x hx => by have := Nat.digits_lt_base hl.one_lt hx; omega)
    rwa [smul_eq_mul, hlen] at this
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl1 : (0 : ℝ) < l - 1 := by linarith
  have e := congrArg (fun t : ℕ => (t : ℝ)) key
  simp only [Nat.cast_mul, Nat.cast_sub hsN, Nat.cast_sub hl.one_le, Nat.cast_one] at e
  have hs1R : (1 : ℝ) ≤ ((l.digits N).sum : ℝ) := by exact_mod_cast hs1
  have hdigR := (Nat.cast_le (α := ℝ)).2 hdig
  simp only [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_add, Nat.cast_one] at hdigR
  have hlog : (Nat.log l N : ℝ) ≤ Real.logb l N := Real.natLog_le_logb N l
  constructor
  · have h : (N : ℝ) / ((l : ℝ) - 1) ≤ (padicValNat l N.factorial : ℝ) + ((Nat.log l N : ℝ) + 1) := by
      rw [div_le_iff₀ hl1]
      nlinarith
    linarith
  · rw [le_div_iff₀ hl1]
    nlinarith

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[← add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma num_fact_add_q (a k : ℕ) :
    (((a + k).factorial : ℕ) : ℚ) = (a.factorial : ℚ) * ∏ j ∈ Finset.range k, ((a : ℚ) + j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[Finset.prod_Ico_eq_prod_range, show m + 1 - 1 = m by omega, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hj : ((j : ℚ) + 1) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma prod_range_eq_factorial_mul_prod_Ico (m x : ℕ) :
    ∏ j ∈ Finset.range m, ((((m + 1) * x : ℕ) : ℚ) + j + 1) =
      (m.factorial : ℚ) * ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ)) := by
  rw [Finset.prod_Ico_eq_prod_range, show m + 1 - 1 = m by omega,
    ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/- English proof (translation)
Unfold `uFac`. Rewrite using `[show (m + 1) * (x + 1) = (m + 1) * x + (m + 1) by ring, num_fact_add_q, Finset.prod_range_succ, prod_range_eq_factorial_mul_prod_Ico m x, Nat.factorial_succ x]`. Establish `h1 : ((m : ℚ) + 1) ≠ 0` using `by positivity`. Establish `h2 : ((x : ℚ) + 1) ≠ 0` using `by positivity`. Establish `h3 : ((x.factorial : ℕ) : ℚ) ≠ 0` using `by positivity`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma num_uFac_succ (m x : ℕ) :
    uFac (m + 1) (x + 1) = uFac (m + 1) x * (-(m.factorial : ℚ) *
      ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ))) := by
  unfold uFac
  rw [show (m + 1) * (x + 1) = (m + 1) * x + (m + 1) by ring, num_fact_add_q,
    Finset.prod_range_succ, prod_range_eq_factorial_mul_prod_Ico m x, Nat.factorial_succ x]
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((x : ℚ) + 1) ≠ 0 := by positivity
  have h3 : ((x.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/- English proof (translation)
Introduce `l hl x`. Take `⟨m, rfl⟩ : ∃ m, l = m + 1` from `⟨l - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Proceed by induction on `x with`. Consider the case `zero => simp [uFac]`.

Consider the case `succ x ih`. Rewrite using `[num_uFac_succ, ih, Finset.prod_range_succ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unitFactorialProd : UProduct := by
  intro l hl x
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction x with
  | zero => simp [uFac]
  | succ x ih =>
    rw [num_uFac_succ, ih, Finset.prod_range_succ, pow_succ]
    ring

/- English proof (translation)
Proceed by induction on `v with`. Consider the case `zero => simp`. Consider the case `succ v ih`. Rewrite using `[pow_succ]`. Use `Nat.one_le_pow v 5 (by norm_num)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
lemma num_one_add_four_mul_le (v : ℕ) : 1 + 4 * v ≤ 5 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    have := Nat.one_le_pow v 5 (by norm_num)
    omega

/- English proof (translation)
Introduce `l hl hl5 s hs`. Use `haveI := Fact.mk hl`. Establish `hdvd : l ^ padicValNat l s ∣ s` using `pow_padicValNat_dvd`. Establish `hle : l ^ padicValNat l s ≤ s` using `Nat.le_of_dvd (by omega) hdvd`. Establish `h5 : 5 ^ padicValNat l s ≤ l ^ padicValNat l s` using `Nat.pow_le_pow_left hl5 _`.

Establish `h4` using `num_one_add_four_mul_le (padicValNat l s)`. Establish `hN : 1 + 4 * padicValNat l s ≤ s` using `by omega`. Establish `hR : (1 : ℝ) + 4 * (padicValNat l s : ℝ) ≤ s` using `by exact_mod_cast hN`. Establish `hl5R : (5 : ℝ) ≤ l` using `by exact_mod_cast hl5`. Establish `h14 : 1 / ((l : ℝ) - 1) ≤ 1 / 4` using `one_div_le_one_div_of_le (by norm_num) (by linarith)`.

Establish `hs1 : (1 : ℝ) ≤ s` using `by exact_mod_cast hs`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logCoeffValuation : LogCoeffVal := by
  intro l hl hl5 s hs
  haveI := Fact.mk hl
  have hdvd : l ^ padicValNat l s ∣ s := pow_padicValNat_dvd
  have hle : l ^ padicValNat l s ≤ s := Nat.le_of_dvd (by omega) hdvd
  have h5 : 5 ^ padicValNat l s ≤ l ^ padicValNat l s := Nat.pow_le_pow_left hl5 _
  have h4 := num_one_add_four_mul_le (padicValNat l s)
  have hN : 1 + 4 * padicValNat l s ≤ s := by omega
  have hR : (1 : ℝ) + 4 * (padicValNat l s : ℝ) ≤ s := by exact_mod_cast hN
  have hl5R : (5 : ℝ) ≤ l := by exact_mod_cast hl5
  have h14 : 1 / ((l : ℝ) - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/- English proof (translation)
Introduce `l hl s0`. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hne : (l : ℝ) ^ 2 ≠ 1` using `by nlinarith`. Establish `hne' : (l : ℝ) ^ 2 - 1 ≠ 0` using `sub_ne_zero.2 hne`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[geom_sum_eq hne, rho, ← pow_mul, pow_succ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `s`. Rewrite using `[Finset.sum_range_succ', Finset.mul_sum, pow_zero]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun t _ => by ring`.
-/
theorem shiftExponentIdentity : LemmaMExponent := by
  intro l hl s0
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hne : (l : ℝ) ^ 2 ≠ 1 := by nlinarith
  have hne' : (l : ℝ) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hne
  refine ⟨?_, ?_⟩
  · rw [geom_sum_eq hne, rho, ← pow_mul, pow_succ]
    field_simp
    ring
  · intro s
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring

/- English proof (translation)
Establish `h` using `one_add_mul_le_pow (show (-2 : ℝ) ≤ a - 1 by linarith) w`. Simplify using `using h`.
-/
lemma num_bern_real (a : ℝ) (ha : 1 ≤ a) (w : ℕ) : 1 + (w : ℝ) * (a - 1) ≤ a ^ w := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ a - 1 by linarith) w
  simpa using h

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `l hl i hi`. Take `⟨k, rfl⟩` from `hi`. Establish `hL : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Use `set L : ℝ := (l : ℝ) with hLdef`. Establish `hL2 : L ^ 2 - 1 ≠ 0` using `by nlinarith`.

Establish `hρpos : 0 < rho l`. Unfold `rho`. Apply `div_pos one_pos` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hρeq : L ^ 2 * rho l = 1 + rho l`.

Unfold `rho`. Rewrite using `[← hLdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hk1 : 1 ≤ L ^ (2 * k)` using `one_le_pow₀ (by linarith)`.

Establish `hLi : L ≤ L ^ (2 * k + 1)` using `by rw [pow_succ]; nlinarith`. Establish `hLipos : 0 < L ^ (2 * k + 1)` using `by positivity`. Establish `hinv : (L ^ (2 * k + 1))⁻¹ ≤ L⁻¹` using `inv_anti₀ (by linarith) hLi`. Establish `hinv5 : L⁻¹ ≤ 5⁻¹` using `inv_anti₀ (by norm_num) hL`. Establish `hinvpos : 0 < (L ^ (2 * k + 1))⁻¹` using `inv_pos.2 hLipos`.

Establish `h14 : 1 / (L - 1) ≤ 1 / 4` using `one_div_le_one_div_of_le (by norm_num) (by linarith)`. Use `⟨hρeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i' hi'`. Take `⟨j, rfl⟩ : ∃ j, i' = j + 3` from `⟨i' - 3, by omega⟩`. Use `push_cast`.

Establish `b` using `num_bern_real L (by linarith) j`. Establish `e : L ^ (j + 3) * rho l = L ^ (j + 1) * (1 + rho l)` using `by rw [← hρeq]; ring`. Establish `hp : 0 < L ^ (j + 1)` using `by positivity`. Establish `h1 : (1 + j * (L - 1)) * L ≤ L ^ j * L` using `mul_le_mul_of_nonneg_right b (by linarith)`. Establish `h3 : (0 : ℝ) ≤ j * (L * (L - 1) - 1)` using `mul_nonneg (Nat.cast_nonneg j) (by nlinarith)`.

Establish `h4 : L ^ (j + 1) ≤ L ^ (j + 1) * (1 + rho l)` using `by nlinarith`. Establish `hpow : L ^ (j + 1) = L ^ j * L` using `pow_succ L j`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `i' hi'`.

Take `⟨j, rfl⟩ : ∃ j, i' = j + 2` from `⟨i' - 2, by omega⟩`. Use `push_cast`. Establish `b` using `num_bern_real L (by linarith) j`. Establish `e : L ^ (j + 2) * rho l = L ^ j * (1 + rho l)` using `by rw [← hρeq]; ring`. Establish `hpj : 0 < L ^ j` using `by positivity`.

Establish `hm` using `mul_pos hpj hρpos`. Establish `h : (0 : ℝ) ≤ j * (L - 5)` using `mul_nonneg (Nat.cast_nonneg j) (by linarith)`. Establish `h25 : L ^ j * 25 ≤ L ^ j * L ^ 2` using `mul_le_mul_of_nonneg_left (by nlinarith) hpj.le`. Establish `hpow : L ^ (j + 2) = L ^ j * L ^ 2` using `pow_add L j 2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Use `mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1) hρpos.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[show (2 * k + 1 + 1) / 2 = k + 1 by omega, ← pow_mul]`. Establish `: L ^ (2 * k + 1) ≠ 0` using `hLipos.ne'`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e8 : (1 : ℝ) / (8 * L) = L⁻¹ / 8` using `by ring`. Rewrite using `[e8]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i' hi'`.

Rewrite using `[lt_div_iff₀ (by linarith : (0 : ℝ) < L - 1)]`. Establish `b` using `num_bern_real L (by linarith) i'`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `J v hJ hv dsimp only`. Establish `hδ : 9 / 40 ≤ rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)` using `by linarith`.

Establish `hJR : (2 : ℝ) ≤ J` using `by exact_mod_cast hJ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `hv0`. Substitute `hv0` using the available equality. Establish `hprod : 0 ≤ ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1))` using `mul_nonneg (by linarith) (by linarith)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hv1`. Take `⟨w, rfl⟩ : ∃ w, v = w + 1` from `⟨v - 1, by omega⟩`. Establish `h5 : 5 ^ (w + 1) ≤ l ^ (w + 1)` using `Nat.pow_le_pow_left (by omega) _`.

Establish `h4` using `num_one_add_four_mul_le w`. Establish `hps : 5 ^ (w + 1) = 5 ^ w * 5` using `pow_succ 5 w`. Establish `hJn : 20 * w + 5 ≤ J` using `by omega`. Establish `hJr : 20 * (w : ℝ) + 5 ≤ J` using `by exact_mod_cast hJn`. Establish `hprod : (20 * (w : ℝ) + 4) * (9 / 40) ≤ ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1))` using `mul_le_mul (by linarith) hδ (by norm_num) (by linarith)`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem weightNumerics : LemmaMNumerics := by
  intro l hl i hi
  obtain ⟨k, rfl⟩ := hi
  have hL : (5 : ℝ) ≤ l := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hL2 : L ^ 2 - 1 ≠ 0 := by nlinarith
  have hρpos : 0 < rho l := by
    unfold rho
    apply div_pos one_pos
    nlinarith
  have hρeq : L ^ 2 * rho l = 1 + rho l := by
    unfold rho
    rw [← hLdef]
    field_simp
    ring
  have hk1 : 1 ≤ L ^ (2 * k) := one_le_pow₀ (by linarith)
  have hLi : L ≤ L ^ (2 * k + 1) := by rw [pow_succ]; nlinarith
  have hLipos : 0 < L ^ (2 * k + 1) := by positivity
  have hinv : (L ^ (2 * k + 1))⁻¹ ≤ L⁻¹ := inv_anti₀ (by linarith) hLi
  have hinv5 : L⁻¹ ≤ 5⁻¹ := inv_anti₀ (by norm_num) hL
  have hinvpos : 0 < (L ^ (2 * k + 1))⁻¹ := inv_pos.2 hLipos
  have h14 : 1 / (L - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨hρeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    obtain ⟨j, rfl⟩ : ∃ j, i' = j + 3 := ⟨i' - 3, by omega⟩
    push_cast
    have b := num_bern_real L (by linarith) j
    have e : L ^ (j + 3) * rho l = L ^ (j + 1) * (1 + rho l) := by rw [← hρeq]; ring
    have hp : 0 < L ^ (j + 1) := by positivity
    have h1 : (1 + j * (L - 1)) * L ≤ L ^ j * L := mul_le_mul_of_nonneg_right b (by linarith)
    have h3 : (0 : ℝ) ≤ j * (L * (L - 1) - 1) := mul_nonneg (Nat.cast_nonneg j) (by nlinarith)
    have h4 : L ^ (j + 1) ≤ L ^ (j + 1) * (1 + rho l) := by nlinarith
    have hpow : L ^ (j + 1) = L ^ j * L := pow_succ L j
    rw [e]
    nlinarith
  · intro i' hi'
    obtain ⟨j, rfl⟩ : ∃ j, i' = j + 2 := ⟨i' - 2, by omega⟩
    push_cast
    have b := num_bern_real L (by linarith) j
    have e : L ^ (j + 2) * rho l = L ^ j * (1 + rho l) := by rw [← hρeq]; ring
    have hpj : 0 < L ^ j := by positivity
    have hm := mul_pos hpj hρpos
    have h : (0 : ℝ) ≤ j * (L - 5) := mul_nonneg (Nat.cast_nonneg j) (by linarith)
    have h25 : L ^ j * 25 ≤ L ^ j * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hpj.le
    have hpow : L ^ (j + 2) = L ^ j * L ^ 2 := pow_add L j 2
    refine ⟨?_, ?_⟩
    · rw [e]
      nlinarith
    · nlinarith
  · have := mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1) hρpos.le
    nlinarith
  · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, ← pow_mul]
    have : L ^ (2 * k + 1) ≠ 0 := hLipos.ne'
    field_simp
    ring
  · linarith
  · linarith
  · have e8 : (1 : ℝ) / (8 * L) = L⁻¹ / 8 := by ring
    rw [e8]
    linarith
  · intro i' hi'
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < L - 1)]
    have b := num_bern_real L (by linarith) i'
    linarith
  · intro J v hJ hv
    dsimp only
    have hδ : 9 / 40 ≤ rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1) := by linarith
    have hJR : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    refine ⟨?_, ?_⟩
    · intro hv0
      subst hv0
      have hprod : 0 ≤ ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)) :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      linarith
    · intro hv1
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have h5 : 5 ^ (w + 1) ≤ l ^ (w + 1) := Nat.pow_le_pow_left (by omega) _
      have h4 := num_one_add_four_mul_le w
      have hps : 5 ^ (w + 1) = 5 ^ w * 5 := pow_succ 5 w
      have hJn : 20 * w + 5 ≤ J := by omega
      have hJr : 20 * (w : ℝ) + 5 ≤ J := by exact_mod_cast hJn
      have hprod : (20 * (w : ℝ) + 4) * (9 / 40) ≤
          ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)) :=
        mul_le_mul (by linarith) hδ (by norm_num) (by linarith)
      push_cast
      nlinarith

end Formalism.IncomingBounds
