import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
import Formalism.HyperbolicPlaceProducts.ArithmeticCountRevised

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.SLP.Final.submoduleCountDed, Formalism.SLP.GlobalBoundRefinements.Final.autCount⟩`.
-/
theorem submodule_automorphism_count : CardSubmodulesAndLinearEquivBounds := ⟨Formalism.SLP.Final.submoduleCountDed, Formalism.SLP.GlobalBoundRefinements.Final.autCount⟩

/- English proof (translation)
Introduce `E _ _ M _ _ _ _ k j hj hk`. Take `⟨hfin, hcard⟩` from `Formalism.SLP.Final.submoduleIndexCountO E M j hj`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hd : 1 ≤ finrank ℚ E` using `Module.finrank_pos`. Establish `hom` using `Formalism.SLP.Final.omegaPow (finrank ℚ E) j hd hj`.

Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hj1 (by exact_mod_cast hk)`. Use `_ = (j : ℝ) ^ ((k : ℝ) + Real.logb 2 (finrank ℚ E)) := by`.

Rewrite using `[Real.rpow_add (by linarith)]; ring`.
-/
theorem ideal_count_statement : CardSubmodulesOfIndexLePow := by
  intro E _ _ M _ _ _ _ k j hj hk
  obtain ⟨hfin, hcard⟩ := Formalism.SLP.Final.submoduleIndexCountO E M j hj
  refine ⟨hfin, ?_⟩
  have hd : 1 ≤ finrank ℚ E := Module.finrank_pos
  have hom := Formalism.SLP.Final.omegaPow (finrank ℚ E) j hd hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc ((({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard : ℕ)) : ℝ)
      ≤ ((finrank ℚ E ^ (Nat.primeFactorsList j).length *
          j ^ finrank (NumberField.RingOfIntegers E) M : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (finrank ℚ E : ℝ) ^ (Nat.primeFactorsList j).length *
          (j : ℝ) ^ finrank (NumberField.RingOfIntegers E) M := by push_cast; ring
    _ ≤ (j : ℝ) ^ Real.logb 2 (finrank ℚ E) * (j : ℝ) ^ (k : ℝ) := by
          gcongr
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hj1 (by exact_mod_cast hk)
    _ = (j : ℝ) ^ ((k : ℝ) + Real.logb 2 (finrank ℚ E)) := by
          rw [Real.rpow_add (by linarith)]; ring

/- English proof (translation)
Use `set X := ((p : ℤ) ^ s) • Y with hX`. Establish `hp0 : (p : ℤ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hbin : (X + 1) ^ q = ∑ m ∈ Finset.range (q + 1), X ^ m * (q.choose m : Matrix (Fin N) (Fin N) ℤ)`. Rewrite using `[(Commute.one_right X).add_pow]`. Simplify using the standard rewrite rules.

Establish `hq2` using `hq.two_le`. Establish `hsplit : ∑ m ∈ Finset.range (q + 1), X ^ m * (q.choose m : Matrix (Fin N) (Fin N) ℤ) = 1 + (q : ℤ) • X + ∑ m ∈ Finset.range (q - 1), (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2)`. Establish `e : q + 1 = (q - 1) + 1 + 1` using `by omega`. Rewrite using `[e, Finset.sum_range_succ', Finset.sum_range_succ']`. Simplify using `only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add, pow_one, Nat.choose_one_right]`.

Establish `e2 : ∀ m, X ^ (m + 1 + 1) * (q.choose (m + 1 + 1) : Matrix (Fin N) (Fin N) ℤ) = (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2)`. Introduce `m`. Rewrite using `[hX, smul_pow, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, mul_comm]`. Simplify using `only [e2]`. Rewrite using `[← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ]`.

Normalize the expressions using the abelian group laws. Establish `hmain : (q : ℤ) • X = -∑ m ∈ Finset.range (q - 1), (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2)`. Use `h` as an intermediate fact. Rewrite `this` using `[add_comm, hbin, hsplit]`. Rewrite using `[eq_neg_iff_add_eq_zero]`.

Establish `h2` using `congrArg (· - 1) this`. Simplify using `only [add_sub_cancel_left, sub_self] at h2`. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws. Distinguish the cases in `hqp : q = p`.

Substitute `hqp` using the available equality. Establish `hterm : ∀ m ∈ Finset.range (q - 1), ((q : ℤ) ^ (s + 2)) ∣ ((q : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_range]`. Rewrite using `[← pow_mul]`.

Distinguish the cases in `hlt : m + 2 < q`. Establish `hc : (q : ℤ) ∣ (q.choose (m + 2) : ℤ)`. Conclude with `hq.dvd_choose_self (by omega) hlt` after adjusting the coercions. Establish `: (q : ℤ) ^ (s + 2) ∣ (q : ℤ) ^ (s * (m + 2)) * q`. Rewrite using `[← pow_succ]; exact pow_dvd_pow _ (by nlinarith)`.

Conclude with `this.trans (mul_dvd_mul_left _ hc)`. Establish `hm2 : m + 2 = q` using `by omega`. Rewrite using `[hm2]`. Apply `Dvd.dvd.mul_right` to reduce the goal to its premises. Apply `pow_dvd_pow` to reduce the goal to its premises.

Establish `: (q - 1) * s ≤ s * q - s`. Rewrite using `[Nat.sub_mul, one_mul, mul_comm]`. Use linear arithmetic over natural numbers and integers. Use `choose c hc using hterm`. Establish `hsum : ∑ m ∈ Finset.range (q - 1), (((q : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) = ((q : ℤ) ^ (s + 2)) • ∑ m ∈ (Finset.range (q - 1)).attach, c m.1 m.2 • Y ^ (m.1 + 2)`.

Rewrite using `[Finset.smul_sum, ← Finset.sum_attach]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hc m.1 m.2, smul_smul]`. Rewrite `hmain` using `[hsum, hX, smul_smul, ← smul_neg]`. Establish `e1 : (q : ℤ) * (q : ℤ) ^ s = (q : ℤ) ^ (s + 1)` using `by ring`.

Establish `e2 : (q : ℤ) ^ (s + 2) = (q : ℤ) ^ (s + 1) * q` using `by ring`. Rewrite `hmain` using `[e1, e2, ← smul_smul]`. Use `⟨_, smul_right_injective _ (pow_ne_zero _ hp0) hmain⟩` and prove the remaining obligations. Establish `hterm : ∀ m ∈ Finset.range (q - 1), ((p : ℤ) ^ (2 * s)) ∣ ((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)`. Introduce `m _`.

Rewrite using `[← pow_mul]`. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow _ (by nlinarith)) _`. Use `choose c hc using hterm`. Establish `hsum : ∑ m ∈ Finset.range (q - 1), (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) = ((p : ℤ) ^ (2 * s)) • ∑ m ∈ (Finset.range (q - 1)).attach, c m.1 m.2 • Y ^ (m.1 + 2)`. Rewrite using `[Finset.smul_sum, ← Finset.sum_attach]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hc m.1 m.2, smul_smul]`. Rewrite `hmain` using `[hsum, hX, smul_comm, ← smul_neg, two_mul, pow_add, ← smul_smul]`. Take `⟨W', hqY⟩ : ∃ W' : Matrix (Fin N) (Fin N) ℤ, (q : ℤ) • Y = ((p : ℤ) ^ s) • W'` from `⟨_, smul_right_injective _ (pow_ne_zero s hp0) hmain⟩`. Establish `hcop : IsCoprime (q : ℤ) ((p : ℤ) ^ s)`.

Apply `IsCoprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.isCoprime_iff_coprime]`. Conclude with `(Nat.coprime_primes hq hp).2 hqp`. Take `⟨a, b, hab⟩` from `hcop`. Use `⟨(p : ℤ) ^ (s - 1) • (a • W' + b • Y), ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show a * (q : ℤ) + (p : ℤ) ^ s * b = 1 by linear_combination hab, one_smul]`. Use `_ = a • ((q : ℤ) • Y) + ((p : ℤ) ^ s) • (b • Y) := by rw [add_smul, smul_smul, smul_smul]`. Use `_ = a • (((p : ℤ) ^ s) • W') + ((p : ℤ) ^ s) • (b • Y) := by rw [hqY]`. Use `_ = ((p : ℤ) ^ s) • (a • W' + b • Y) := by rw [smul_add, smul_comm a]`.

Use `_ = (p : ℤ) • ((p : ℤ) ^ (s - 1) • (a • W' + b • Y)) := by`. Rewrite using `[smul_smul, ← pow_succ', Nat.sub_add_cancel hs]`.
-/
private theorem fo_step_lemma (N p q s : ℕ) (hp : p.Prime) (hq : q.Prime) (hs : 1 ≤ s)
    (hps : 2 ≤ (p - 1) * s) (Y : Matrix (Fin N) (Fin N) ℤ)
    (h : (1 + ((p : ℤ) ^ s) • Y) ^ q = 1) : ∃ W : Matrix (Fin N) (Fin N) ℤ, Y = (p : ℤ) • W := by
  set X := ((p : ℤ) ^ s) • Y with hX
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hbin : (X + 1) ^ q = ∑ m ∈ Finset.range (q + 1), X ^ m * (q.choose m : Matrix (Fin N) (Fin N) ℤ) := by
    rw [(Commute.one_right X).add_pow]; simp
  have hq2 := hq.two_le
  have hsplit : ∑ m ∈ Finset.range (q + 1), X ^ m * (q.choose m : Matrix (Fin N) (Fin N) ℤ) =
      1 + (q : ℤ) • X + ∑ m ∈ Finset.range (q - 1),
        (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) := by
    have e : q + 1 = (q - 1) + 1 + 1 := by omega
    rw [e, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add, pow_one,
      Nat.choose_one_right]
    have e2 : ∀ m, X ^ (m + 1 + 1) * (q.choose (m + 1 + 1) : Matrix (Fin N) (Fin N) ℤ) =
        (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) := by
      intro m
      rw [hX, smul_pow, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, mul_comm]
    simp only [e2]
    rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ]
    abel
  have hmain : (q : ℤ) • X = -∑ m ∈ Finset.range (q - 1),
      (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) := by
    have := h
    rw [add_comm, hbin, hsplit] at this
    rw [eq_neg_iff_add_eq_zero]
    have h2 := congrArg (· - 1) this
    simp only [add_sub_cancel_left, sub_self] at h2
    rw [← h2]; abel
  by_cases hqp : q = p
  · subst hqp

    have hterm : ∀ m ∈ Finset.range (q - 1),
        ((q : ℤ) ^ (s + 2)) ∣ ((q : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ) := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [← pow_mul]
      by_cases hlt : m + 2 < q
      · have hc : (q : ℤ) ∣ (q.choose (m + 2) : ℤ) := by
          exact_mod_cast hq.dvd_choose_self (by omega) hlt
        have : (q : ℤ) ^ (s + 2) ∣ (q : ℤ) ^ (s * (m + 2)) * q := by
          rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
        exact this.trans (mul_dvd_mul_left _ hc)
      · have hm2 : m + 2 = q := by omega
        rw [hm2]
        apply Dvd.dvd.mul_right
        apply pow_dvd_pow
        have : (q - 1) * s ≤ s * q - s := by
          rw [Nat.sub_mul, one_mul, mul_comm]
        omega
    choose c hc using hterm
    have hsum : ∑ m ∈ Finset.range (q - 1),
        (((q : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) =
        ((q : ℤ) ^ (s + 2)) • ∑ m ∈ (Finset.range (q - 1)).attach, c m.1 m.2 • Y ^ (m.1 + 2) := by
      rw [Finset.smul_sum, ← Finset.sum_attach]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc m.1 m.2, smul_smul]
    rw [hsum, hX, smul_smul, ← smul_neg] at hmain
    have e1 : (q : ℤ) * (q : ℤ) ^ s = (q : ℤ) ^ (s + 1) := by ring
    have e2 : (q : ℤ) ^ (s + 2) = (q : ℤ) ^ (s + 1) * q := by ring
    rw [e1, e2, ← smul_smul] at hmain
    refine ⟨_, smul_right_injective _ (pow_ne_zero _ hp0) hmain⟩
  ·
    have hterm : ∀ m ∈ Finset.range (q - 1),
        ((p : ℤ) ^ (2 * s)) ∣ ((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ) := by
      intro m _
      rw [← pow_mul]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by nlinarith)) _
    choose c hc using hterm
    have hsum : ∑ m ∈ Finset.range (q - 1),
        (((p : ℤ) ^ s) ^ (m + 2) * (q.choose (m + 2) : ℤ)) • Y ^ (m + 2) =
        ((p : ℤ) ^ (2 * s)) • ∑ m ∈ (Finset.range (q - 1)).attach, c m.1 m.2 • Y ^ (m.1 + 2) := by
      rw [Finset.smul_sum, ← Finset.sum_attach]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc m.1 m.2, smul_smul]
    rw [hsum, hX, smul_comm, ← smul_neg, two_mul, pow_add, ← smul_smul] at hmain
    obtain ⟨W', hqY⟩ : ∃ W' : Matrix (Fin N) (Fin N) ℤ, (q : ℤ) • Y = ((p : ℤ) ^ s) • W' :=
      ⟨_, smul_right_injective _ (pow_ne_zero s hp0) hmain⟩
    have hcop : IsCoprime (q : ℤ) ((p : ℤ) ^ s) := by
      apply IsCoprime.pow_right
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes hq hp).2 hqp
    obtain ⟨a, b, hab⟩ := hcop
    refine ⟨(p : ℤ) ^ (s - 1) • (a • W' + b • Y), ?_⟩
    calc Y = (a * q + (p : ℤ) ^ s * b) • Y := by
          rw [show a * (q : ℤ) + (p : ℤ) ^ s * b = 1 by linear_combination hab, one_smul]
      _ = a • ((q : ℤ) • Y) + ((p : ℤ) ^ s) • (b • Y) := by rw [add_smul, smul_smul, smul_smul]
      _ = a • (((p : ℤ) ^ s) • W') + ((p : ℤ) ^ s) • (b • Y) := by rw [hqY]
      _ = ((p : ℤ) ^ s) • (a • W' + b • Y) := by rw [smul_add, smul_comm a]
      _ = (p : ℤ) • ((p : ℤ) ^ (s - 1) • (a • W' + b • Y)) := by
          rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hs]

/- English proof (translation)
Establish `hall : ∀ k : ℕ, ∃ Y : Matrix (Fin N) (Fin N) ℤ, A = 1 + ((p : ℤ) ^ (s0 + k)) • Y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using h0`. Consider the case `succ k ih`.

Take `⟨Y, hY⟩` from `ih`. Take `⟨W, hW⟩` from `fo_step_lemma N p q (s0 + k) hp hq (by omega) (le_trans hps (Nat.mul_le_mul_left _ (by omega))) Y (hY ▸ hA)`. Use `⟨W, ?_⟩` and prove the remaining obligations. Rewrite using `[hY, hW, smul_smul, ← pow_succ, ← add_assoc]`. Use extensionality with `i j`.

Establish `hdv : ∀ k : ℕ, ((p : ℤ) ^ k) ∣ (A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j)`. Introduce `k`. Take `⟨Y, hY⟩` from `hall k`. Establish `: A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j = (p : ℤ) ^ (s0 + k) * Y i j`. Rewrite using `[hY, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(pow_dvd_pow _ (by omega)).trans (dvd_mul_right _ _)`. Use `set e := A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j`. Establish `: e = 0`.

Apply `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdv e.natAbs)` to reduce the goal to its premises. Rewrite using `[Int.natAbs_pow, Int.natAbs_natCast]`. Conclude with `Nat.lt_pow_self hp.one_lt`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem fo_zero_lemma_2 (N p q s0 : ℕ) (hp : p.Prime) (hq : q.Prime) (hs0 : 1 ≤ s0)
    (hps : 2 ≤ (p - 1) * s0) (A : Matrix (Fin N) (Fin N) ℤ) (hA : A ^ q = 1)
    (h0 : ∃ Y : Matrix (Fin N) (Fin N) ℤ, A = 1 + ((p : ℤ) ^ s0) • Y) : A = 1 := by
  have hall : ∀ k : ℕ, ∃ Y : Matrix (Fin N) (Fin N) ℤ, A = 1 + ((p : ℤ) ^ (s0 + k)) • Y := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      obtain ⟨Y, hY⟩ := ih
      obtain ⟨W, hW⟩ := fo_step_lemma N p q (s0 + k) hp hq (by omega)
        (le_trans hps (Nat.mul_le_mul_left _ (by omega))) Y (hY ▸ hA)
      refine ⟨W, ?_⟩
      rw [hY, hW, smul_smul, ← pow_succ, ← add_assoc]
  ext i j
  have hdv : ∀ k : ℕ, ((p : ℤ) ^ k) ∣ (A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j) := by
    intro k
    obtain ⟨Y, hY⟩ := hall k
    have : A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j = (p : ℤ) ^ (s0 + k) * Y i j := by
      rw [hY, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact (pow_dvd_pow _ (by omega)).trans (dvd_mul_right _ _)
  set e := A i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j
  have : e = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdv e.natAbs)
    rw [Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.lt_pow_self hp.one_lt
  linarith

/- English proof (translation)
Introduce `N n g A B hg hn hA hAB`. Assume the negation of the conclusion as `hne`. Establish `hpow : ∀ k : ℕ, ∃ C : Matrix (Fin N) (Fin N) ℤ, A ^ k = 1 + g • C`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨C, hC⟩` from `ih`. Use `⟨C + B + g • (C * B), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, hC, hAB]`.

Simplify using `only [smul_add, mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]`. Normalize the expressions using the abelian group laws. Establish `hfin : IsOfFinOrder A` using `isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hA⟩`. Establish `ho : orderOf A ≠ 1` using `by rw [Ne, orderOf_eq_one_iff]; exact hne`. Take `⟨q, hq, hqo⟩` from `Nat.exists_prime_and_dvd ho`.

Establish `hopos` using `hfin.orderOf_pos`. Use `set A' := A ^ (orderOf A / q) with hA'`. Establish `hA'q : A' ^ q = 1`. Rewrite using `[hA', ← pow_mul, Nat.div_mul_cancel hqo, pow_orderOf_eq_one]`. Establish `hA'ne : A' ≠ 1`.

Apply `pow_ne_one_of_lt_orderOf` to reduce the goal to its premises. Conclude with `(Nat.div_pos (Nat.le_of_dvd hopos hqo) hq.pos).ne'`. Conclude with `Nat.div_lt_self hopos hq.one_lt`. Take `⟨C, hC⟩` from `hpow (orderOf A / q)`. Rewrite `hC` using `[← hA']`.

Take `⟨G, rfl⟩ : ∃ G : ℕ, g = (G : ℤ)` from `⟨g.toNat, by omega⟩`. Establish `hG : 3 ≤ G` using `by exact_mod_cast hg`. Establish `key : ∃ p s0 : ℕ, p.Prime ∧ 1 ≤ s0 ∧ 2 ≤ (p - 1) * s0 ∧ p ^ s0 ∣ G`. Distinguish the cases in `h4 : 4 ∣ G`. Conclude with `⟨2, 2, Nat.prime_two, by norm_num, by norm_num, by simpa using h4⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨H, hH, hHodd, hH3⟩ : ∃ H, H ∣ G ∧ ¬ 2 ∣ H ∧ 3 ≤ H := by`. Distinguish the cases in `h2 : 2 ∣ G`. Take `⟨h, rfl⟩` from `h2`. Use `⟨h, dvd_mul_left h 2, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨k, rfl⟩; exact h4 ⟨k, by ring⟩`.

Apply the tactic sequence `by_contra hlt interval_cases h <;> simp_all`. Conclude with `⟨G, dvd_rfl, h2, hG⟩`. Establish `hpH` using `Nat.minFac_dvd H`. Establish `hp` using `Nat.minFac_prime (show H ≠ 1 by omega)`. Establish `hp2 : H.minFac ≠ 2`.

Introduce `h`. Rewrite `hpH` using `[h]`. Conclude with `hHodd hpH`. Establish `hp3 : 3 ≤ H.minFac` using `by have := hp.two_le; omega`. Conclude with `⟨H.minFac, 1, hp, le_rfl, by omega, by simpa using hpH.trans hH⟩`.

Take `⟨p, s0, hp, hs0, hps, hdvd⟩` from `key`. Take `⟨G', hG'⟩` from `hdvd`. Establish `hform : A' = 1 + ((p : ℤ) ^ s0) • ((G' : ℤ) • C)`. Rewrite using `[hC, smul_smul, hG']`. Use `push_cast`.

Put the polynomial expressions in normal form. Conclude with `hA'ne (fo_zero_lemma_2 N p q s0 hp hq hs0 hps A' hA'q ⟨_, hform⟩)`.
-/
theorem finite_order_congruence : FiniteOrderCongruence := by
  intro N n g A B hg hn hA hAB
  by_contra hne

  have hpow : ∀ k : ℕ, ∃ C : Matrix (Fin N) (Fin N) ℤ, A ^ k = 1 + g • C := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C + B + g • (C * B), ?_⟩
      rw [pow_succ, hC, hAB]
      simp only [smul_add, mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
        smul_smul]
      abel

  have hfin : IsOfFinOrder A := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hA⟩
  have ho : orderOf A ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact hne
  obtain ⟨q, hq, hqo⟩ := Nat.exists_prime_and_dvd ho
  have hopos := hfin.orderOf_pos
  set A' := A ^ (orderOf A / q) with hA'
  have hA'q : A' ^ q = 1 := by
    rw [hA', ← pow_mul, Nat.div_mul_cancel hqo, pow_orderOf_eq_one]
  have hA'ne : A' ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hopos hqo) hq.pos).ne'
    · exact Nat.div_lt_self hopos hq.one_lt
  obtain ⟨C, hC⟩ := hpow (orderOf A / q)
  rw [← hA'] at hC

  obtain ⟨G, rfl⟩ : ∃ G : ℕ, g = (G : ℤ) := ⟨g.toNat, by omega⟩
  have hG : 3 ≤ G := by exact_mod_cast hg
  have key : ∃ p s0 : ℕ, p.Prime ∧ 1 ≤ s0 ∧ 2 ≤ (p - 1) * s0 ∧ p ^ s0 ∣ G := by
    by_cases h4 : 4 ∣ G
    · exact ⟨2, 2, Nat.prime_two, by norm_num, by norm_num, by simpa using h4⟩
    · obtain ⟨H, hH, hHodd, hH3⟩ : ∃ H, H ∣ G ∧ ¬ 2 ∣ H ∧ 3 ≤ H := by
        by_cases h2 : 2 ∣ G
        · obtain ⟨h, rfl⟩ := h2
          refine ⟨h, dvd_mul_left h 2, ?_, ?_⟩
          · rintro ⟨k, rfl⟩; exact h4 ⟨k, by ring⟩
          · by_contra hlt
            interval_cases h <;> simp_all
        · exact ⟨G, dvd_rfl, h2, hG⟩
      have hpH := Nat.minFac_dvd H
      have hp := Nat.minFac_prime (show H ≠ 1 by omega)
      have hp2 : H.minFac ≠ 2 := by
        intro h; rw [h] at hpH; exact hHodd hpH
      have hp3 : 3 ≤ H.minFac := by have := hp.two_le; omega
      exact ⟨H.minFac, 1, hp, le_rfl, by omega, by simpa using hpH.trans hH⟩
  obtain ⟨p, s0, hp, hs0, hps, hdvd⟩ := key
  obtain ⟨G', hG'⟩ := hdvd
  have hform : A' = 1 + ((p : ℤ) ^ s0) • ((G' : ℤ) • C) := by
    rw [hC, smul_smul, hG']; push_cast; ring_nf
  exact hA'ne (fo_zero_lemma_2 N p q s0 hp hq hs0 hps A' hA'q ⟨_, hform⟩)

/- English proof (translation)
Use `Finset.induction_on S (by simp) ?_` and prove the remaining obligations. Introduce `a S ha ih hS h`. Rewrite using `[Finset.prod_insert ha]`. Apply `Nat.Coprime.mul_dvd_of_dvd_of_dvd` to reduce the goal to its premises. Apply `Nat.Coprime.prod_right` to reduce the goal to its premises.

Introduce `q hq`. Apply `Nat.Coprime.pow` to reduce the goal to its premises. Conclude with `(Nat.coprime_primes (hS a (by simp)) (hS q (by simp [hq]))).2 (by rintro rfl; exact ha hq)`. Conclude with `h a (by simp)`. Conclude with `ih (fun p hp => hS p (by simp [hp])) (fun p hp => h p (by simp [hp]))`.
-/
private theorem prod_pow_dvd_lemma (S : Finset ℕ) (e : ℕ → ℕ) (n : ℕ) :
    (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ^ e p ∣ n) → ∏ p ∈ S, p ^ e p ∣ n := by
  refine Finset.induction_on S (by simp) ?_
  intro a S ha ih hS h
  rw [Finset.prod_insert ha]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  · apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes (hS a (by simp)) (hS q (by simp [hq]))).2
      (by rintro rfl; exact ha hq)
  · exact h a (by simp)
  · exact ih (fun p hp => hS p (by simp [hp])) (fun p hp => h p (by simp [hp]))

/- English proof (translation)
Introduce `N`. Unfold `minkowskiNumber`. Apply `prod_pow_dvd_lemma` to reduce the goal to its premises. Introduce `p hp`. Conclude with `(Finset.mem_filter.1 hp).2`.

Introduce `p hpS`. Establish `hp : p.Prime` using `(Finset.mem_filter.1 hpS).2`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using the standard rewrite rules. Establish `h2 : N < 2 ^ N` using `by clear hpS hp hN`.

Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hlt : 2 * N < p ^ (N + 2)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlog : Nat.log p (2 * N) < N + 2` using `Nat.log_lt_of_lt_pow (by omega) hlt`. Rewrite using `[hp.pow_dvd_factorial_iff hlog, Finset.sum_Ico_eq_sum_range]`. Establish `e : N + 2 - 1 = N + 1` using `by omega`. Rewrite using `[e]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `k _`. Establish `hp2` using `hp.two_le`. Establish `hpk : 0 < p ^ k` using `pow_pos hp.pos k`. Rewrite using `[Nat.le_div_iff_mul_le (pow_pos hp.pos _)]`.

Establish `h1` using `Nat.div_mul_le_self N (p ^ k * (p - 1))`. Establish `h3 : p ^ (1 + k) ≤ 2 * (p ^ k * (p - 1))`. Rewrite using `[pow_add, pow_one]`. Establish `: p ≤ 2 * (p - 1)` using `by omega`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem minkowski_number_dvd : MinkowskiNumberDvd := by
  intro N
  unfold minkowskiNumber
  apply prod_pow_dvd_lemma
  · intro p hp; exact (Finset.mem_filter.1 hp).2
  intro p hpS
  have hp : p.Prime := (Finset.mem_filter.1 hpS).2
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h2 : N < 2 ^ N := by
    clear hpS hp hN
    induction N with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have hlt : 2 * N < p ^ (N + 2) := by
    calc 2 * N < 2 ^ (N + 2) := by rw [pow_add]; omega
      _ ≤ p ^ (N + 2) := Nat.pow_le_pow_left hp.two_le _
  have hlog : Nat.log p (2 * N) < N + 2 := Nat.log_lt_of_lt_pow (by omega) hlt
  rw [hp.pow_dvd_factorial_iff hlog, Finset.sum_Ico_eq_sum_range]
  have e : N + 2 - 1 = N + 1 := by omega
  rw [e]
  apply Finset.sum_le_sum
  intro k _
  have hp2 := hp.two_le
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  rw [Nat.le_div_iff_mul_le (pow_pos hp.pos _)]
  have h1 := Nat.div_mul_le_self N (p ^ k * (p - 1))
  have h3 : p ^ (1 + k) ≤ 2 * (p ^ k * (p - 1)) := by
    rw [pow_add, pow_one]
    have : p ≤ 2 * (p - 1) := by omega
    calc p * p ^ k ≤ 2 * (p - 1) * p ^ k := Nat.mul_le_mul_right _ this
      _ = 2 * (p ^ k * (p - 1)) := by ring
  calc N / (p ^ k * (p - 1)) * p ^ (1 + k)
      ≤ N / (p ^ k * (p - 1)) * (2 * (p ^ k * (p - 1))) := Nat.mul_le_mul_left _ h3
    _ = 2 * (N / (p ^ k * (p - 1)) * (p ^ k * (p - 1))) := by ring
    _ ≤ 2 * N := Nat.mul_le_mul_left _ h1

/- English proof (translation)
Establish `hn : Ideal.absNorm I ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hfin : {P : Ideal (NumberField.RingOfIntegers K) | P.IsPrime ∧ I ≤ P}.Finite`. Apply `Set.Finite.subset ((Ideal.absNorm I).divisors.finite_toSet.biUnion fun d hd => Ideal.finite_setOf_absNorm_eq d)` to reduce the goal to its premises. Introduce `P hP`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_divisors]`.

Conclude with `⟨_, ⟨Ideal.absNorm_dvd_absNorm_of_le hP.2, hn⟩, rfl⟩`. Use `⟨hfin.toFinset, by simp, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Rewrite `hP` using `[Set.Finite.mem_toFinset]`. Conclude with `⟨hP.1, fun h => hI (le_bot_iff.1 (h ▸ hP.2)), hP.2⟩`.

Rewrite using `[← map_prod]`. Apply `map_dvd` to reduce the goal to its premises. Apply `Finset.prod_primes_dvd` to reduce the goal to its premises. Introduce `P hP`. Rewrite `hP` using `[Set.Finite.mem_toFinset]`.

Use `haveI := hP.1`. Conclude with `Ideal.prime_of_isPrime (fun h => hI (le_bot_iff.1 (h ▸ hP.2))) hP.1`. Introduce `P hP`. Rewrite `hP` using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_iff_le.2 hP.2`.
-/
private theorem primeSet_lemma (K : Type) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    ∃ T : Finset (Ideal (NumberField.RingOfIntegers K)),
      (↑T : Set _) = {P | P.IsPrime ∧ I ≤ P} ∧ (∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ ∧ I ≤ P) ∧
      ∏ P ∈ T, Ideal.absNorm P ∣ Ideal.absNorm I := by
  have hn : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hfin : {P : Ideal (NumberField.RingOfIntegers K) | P.IsPrime ∧ I ≤ P}.Finite := by
    apply Set.Finite.subset ((Ideal.absNorm I).divisors.finite_toSet.biUnion
      fun d hd => Ideal.finite_setOf_absNorm_eq d)
    intro P hP
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_divisors]
    exact ⟨_, ⟨Ideal.absNorm_dvd_absNorm_of_le hP.2, hn⟩, rfl⟩
  refine ⟨hfin.toFinset, by simp, ?_, ?_⟩
  · intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact ⟨hP.1, fun h => hI (le_bot_iff.1 (h ▸ hP.2)), hP.2⟩
  · rw [← map_prod]
    apply map_dvd
    apply Finset.prod_primes_dvd
    · intro P hP
      rw [Set.Finite.mem_toFinset] at hP
      haveI := hP.1
      exact Ideal.prime_of_isPrime (fun h => hI (le_bot_iff.1 (h ▸ hP.2))) hP.1
    · intro P hP
      rw [Set.Finite.mem_toFinset] at hP
      exact Ideal.dvd_iff_le.2 hP.2

open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn`. Break down `Nat.lt_or_ge n 2 with h | h` into its components or cases.

Establish `h1 : n = 1` using `by omega`. Substitute `h1` using the available equality. Establish `: {I : Ideal (𝓞 K) | Ideal.absNorm I = 1} = {⊤}`. Use extensionality with `I`. Simplify using `[Ideal.absNorm_eq_one_iff]`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hd : 0 < finrank ℚ K` using `Module.finrank_pos`. Establish `hp : n.minFac.Prime` using `Nat.minFac_prime (by omega)`. Establish `hpn : n.minFac ∣ n` using `Nat.minFac_dvd n`.

Use `set p := n.minFac with hpdef`. Use `set q : 𝓞 K := (p : 𝓞 K) with hqdef`. Establish `hq0 : q ≠ 0` using `by rw [hqdef]; exact_mod_cast hp.ne_zero`. Establish `hqbot : Ideal.span {q} ≠ ⊥` using `by rwa [Ne, Ideal.span_singleton_eq_bot]`. Establish `hNq : Ideal.absNorm (Ideal.span {q}) = p ^ finrank ℚ K`.

Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: q = algebraMap ℤ (𝓞 K) (p : ℤ)` using `by simp [hqdef]`. Rewrite using `[this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]`. Simplify using the standard rewrite rules. Take `⟨T, hT, hT2, hprod⟩` from `primeSet_lemma K (Ideal.span {q}) hqbot`.

Rewrite `hprod` using `[hNq]`. Establish `hNP : ∀ P ∈ T, 2 ≤ Ideal.absNorm P ∧ p ≤ Ideal.absNorm P`. Introduce `P hP`. Take `⟨h1, h2, _⟩` from `hT2 P hP`. Establish `a : Ideal.absNorm P ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`.

Establish `b : Ideal.absNorm P ≠ 1` using `by rw [Ne, Ideal.absNorm_eq_one_iff]; exact h1.ne_top`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Take `⟨k, _, hk⟩` from `(Nat.dvd_prime_pow hp).1 ((Finset.dvd_prod_of_mem _ hP).trans hprod)`. Establish `hk0 : k ≠ 0` using `by rintro rfl; rw [pow_zero] at hk; exact b hk`. Rewrite using `[hk]`.

Conclude with `Nat.le_self_pow hk0 p`. Establish `hTcard : T.card ≤ finrank ℚ K`. Establish `h1 : p ^ T.card ≤ ∏ P ∈ T, Ideal.absNorm P` using `Finset.pow_card_le_prod _ _ _ fun P hP => (hNP P hP).2`. Establish `h2 : ∏ P ∈ T, Ideal.absNorm P ≤ p ^ finrank ℚ K` using `Nat.le_of_dvd (pow_pos hp.pos _) hprod`. Conclude with `(Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h2)`.

Establish `hcover : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → ∃ P ∈ T, Ideal.absNorm P ∣ n ∧ ∃ J, Ideal.absNorm J = n / Ideal.absNorm P ∧ I = P * J`. Introduce `I hI`. Establish `key : I ⊔ Ideal.span {q} ≠ ⊤`. Introduce `htop`. Establish `hcard : Nat.card (𝓞 K ⧸ I) = n`.

Rewrite using `[← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by omega)`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨y, hy⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ I) p (hcard ▸ hpn)`. Establish `h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {q}` using `htop ▸ Submodule.mem_top`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 h1`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Establish `hu : Ideal.Quotient.mk I r * (p : 𝓞 K ⧸ I) = 1`. Use `congrArg (Ideal.Quotient.mk I) hab` as an intermediate fact. Rewrite `this` using `[map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, map_one]`.

Simplify `this` using `[hqdef]`. Establish `hpy : (p : 𝓞 K ⧸ I) * y = 0`. Rewrite using `[← nsmul_eq_mul, ← hy]`. Conclude with `addOrderOf_nsmul_eq_zero y`. Establish `hy0 : y = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hy` using `[hy0, addOrderOf_zero]`. Conclude with `hp.one_lt.ne hy`. Take `⟨P, hPmax, hPle⟩` from `Ideal.exists_le_maximal _ key`. Establish `hPT : P ∈ T`.

Establish `: P ∈ (↑T : Set (Ideal (𝓞 K)))`. Rewrite using `[hT]`. Conclude with `⟨hPmax.isPrime, le_trans le_sup_right hPle⟩`. Conclude with `this`. Take `⟨J, rfl⟩` from `Ideal.dvd_iff_le.2 (le_trans le_sup_left hPle)`.

Rewrite `hI` using `[map_mul]`. Establish `hP0 : 0 < Ideal.absNorm P` using `by have := hNP P hPT; omega`. Use `⟨P, hPT, ⟨_, hI.symm⟩, J, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← hI, Nat.mul_div_cancel_left _ hP0]`. Set `T'` to `T.filter (fun P => Ideal.absNorm P ∣ n)`.

Set `F` to `T'.biUnion (fun P => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n / Ideal.absNorm P)).toFinset.image (P * ·))`. Establish `hsub : {I : Ideal (𝓞 K) | Ideal.absNorm I = n} ⊆ ↑F`. Introduce `I hI`. Take `⟨P, hPT, hdvd, J, hJ, rfl⟩` from `hcover I hI`. Simplify using `only [F, T', Finset.coe_biUnion, Finset.coe_filter, Set.mem_iUnion, Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]`.

Conclude with `⟨P, ⟨hPT, hdvd⟩, J, hJ, rfl⟩`. Establish `hΩ : 1 ≤ (Nat.primeFactorsList n).length`. Establish `: Nat.primeFactorsList n ≠ []`. Rewrite using `[Ne, Nat.primeFactorsList_eq_nil]`. Use linear arithmetic over natural numbers and integers.

Conclude with `List.length_pos_iff.2 this`. Establish `hterm : ∀ P ∈ T', (Ideal.finite_setOf_absNorm_eq (S` using `𝓞 K) (n / Ideal.absNorm P)).toFinset.card ≤ finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := by`. Introduce `P hP`. Take `⟨hPT, hdvd⟩` from `Finset.mem_filter.1 hP`. Take `⟨h2, _⟩` from `hNP P hPT`.

Take `⟨m, hm⟩` from `hdvd`. Establish `hm0 : m ≠ 0` using `by rintro rfl; omega`. Establish `hmdiv : n / Ideal.absNorm P = m` using `by rw [hm, Nat.mul_div_cancel_left _ (by omega)]`. Rewrite using `[← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq _), hmdiv]`. Establish `hmlt : m < n`.

Rewrite using `[hm]; have : 1 * m < Ideal.absNorm P * m := by`. Apply `Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Use `(ih m hmlt (Nat.one_le_iff_ne_zero.2 hm0)).trans (Nat.pow_le_pow_right hd ?_)` and prove the remaining obligations. Establish `hlen` using `(Nat.perm_primeFactorsList_mul (a := Ideal.absNorm P) (b := m) (by omega) hm0).length_eq`.

Rewrite `hlen` using `[← hm, List.length_append]`. Establish `: 1 ≤ (Nat.primeFactorsList (Ideal.absNorm P)).length`. Establish `: Nat.primeFactorsList (Ideal.absNorm P) ≠ []`. Rewrite using `[Ne, Nat.primeFactorsList_eq_nil]`. Use linear arithmetic over natural numbers and integers.

Conclude with `List.length_pos_iff.2 this`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_succ']`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem normCount_lemma (K : Type) [Field K] [NumberField K] : ∀ n : ℕ, 1 ≤ n →
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard ≤
      finrank ℚ K ^ (Nat.primeFactorsList n).length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have : {I : Ideal (𝓞 K) | Ideal.absNorm I = 1} = {⊤} := by
      ext I; simp [Ideal.absNorm_eq_one_iff]
    rw [this]; simp
  have hd : 0 < finrank ℚ K := Module.finrank_pos
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  set p := n.minFac with hpdef
  set q : 𝓞 K := (p : 𝓞 K) with hqdef
  have hq0 : q ≠ 0 := by rw [hqdef]; exact_mod_cast hp.ne_zero
  have hqbot : Ideal.span {q} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hNq : Ideal.absNorm (Ideal.span {q}) = p ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : q = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp [hqdef]
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  obtain ⟨T, hT, hT2, hprod⟩ := primeSet_lemma K (Ideal.span {q}) hqbot
  rw [hNq] at hprod
  have hNP : ∀ P ∈ T, 2 ≤ Ideal.absNorm P ∧ p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨h1, h2, _⟩ := hT2 P hP
    have a : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have b : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact h1.ne_top
    refine ⟨by omega, ?_⟩
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 ((Finset.dvd_prod_of_mem _ hP).trans hprod)
    have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; exact b hk
    rw [hk]; exact Nat.le_self_pow hk0 p
  have hTcard : T.card ≤ finrank ℚ K := by
    have h1 : p ^ T.card ≤ ∏ P ∈ T, Ideal.absNorm P :=
      Finset.pow_card_le_prod _ _ _ fun P hP => (hNP P hP).2
    have h2 : ∏ P ∈ T, Ideal.absNorm P ≤ p ^ finrank ℚ K :=
      Nat.le_of_dvd (pow_pos hp.pos _) hprod
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h2)

  have hcover : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n →
      ∃ P ∈ T, Ideal.absNorm P ∣ n ∧ ∃ J, Ideal.absNorm J = n / Ideal.absNorm P ∧ I = P * J := by
    intro I hI
    have key : I ⊔ Ideal.span {q} ≠ ⊤ := by
      intro htop
      have hcard : Nat.card (𝓞 K ⧸ I) = n := by
        rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by omega)
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ I) p (hcard ▸ hpn)
      have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {q} := htop ▸ Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      have hu : Ideal.Quotient.mk I r * (p : 𝓞 K ⧸ I) = 1 := by
        have := congrArg (Ideal.Quotient.mk I) hab
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, map_one] at this
        simpa [hqdef] using this
      have hpy : (p : 𝓞 K ⧸ I) * y = 0 := by
        rw [← nsmul_eq_mul, ← hy]; exact addOrderOf_nsmul_eq_zero y
      have hy0 : y = 0 := by
        calc y = (Ideal.Quotient.mk I r * (p : 𝓞 K ⧸ I)) * y := by rw [hu, one_mul]
          _ = Ideal.Quotient.mk I r * ((p : 𝓞 K ⧸ I) * y) := by ring
          _ = 0 := by rw [hpy, mul_zero]
      rw [hy0, addOrderOf_zero] at hy
      exact hp.one_lt.ne hy
    obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ key
    have hPT : P ∈ T := by
      have : P ∈ (↑T : Set (Ideal (𝓞 K))) := by
        rw [hT]; exact ⟨hPmax.isPrime, le_trans le_sup_right hPle⟩
      exact this
    obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 (le_trans le_sup_left hPle)
    rw [map_mul] at hI
    have hP0 : 0 < Ideal.absNorm P := by have := hNP P hPT; omega
    refine ⟨P, hPT, ⟨_, hI.symm⟩, J, ?_, rfl⟩
    rw [← hI, Nat.mul_div_cancel_left _ hP0]

  classical
  let T' := T.filter (fun P => Ideal.absNorm P ∣ n)
  let F := T'.biUnion (fun P =>
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n / Ideal.absNorm P)).toFinset.image (P * ·))
  have hsub : {I : Ideal (𝓞 K) | Ideal.absNorm I = n} ⊆ ↑F := by
    intro I hI
    obtain ⟨P, hPT, hdvd, J, hJ, rfl⟩ := hcover I hI
    simp only [F, T', Finset.coe_biUnion, Finset.coe_filter, Set.mem_iUnion, Finset.coe_image,
      Set.Finite.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨P, ⟨hPT, hdvd⟩, J, hJ, rfl⟩
  have hΩ : 1 ≤ (Nat.primeFactorsList n).length := by
    have : Nat.primeFactorsList n ≠ [] := by
      rw [Ne, Nat.primeFactorsList_eq_nil]; omega
    exact List.length_pos_iff.2 this
  have hterm : ∀ P ∈ T', (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K)
      (n / Ideal.absNorm P)).toFinset.card ≤
        finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := by
    intro P hP
    obtain ⟨hPT, hdvd⟩ := Finset.mem_filter.1 hP
    obtain ⟨h2, _⟩ := hNP P hPT
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hmdiv : n / Ideal.absNorm P = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
    rw [← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq _), hmdiv]
    have hmlt : m < n := by
      rw [hm]; have : 1 * m < Ideal.absNorm P * m := by
        apply Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      omega
    refine (ih m hmlt (Nat.one_le_iff_ne_zero.2 hm0)).trans (Nat.pow_le_pow_right hd ?_)
    have hlen := (Nat.perm_primeFactorsList_mul (a := Ideal.absNorm P) (b := m)
      (by omega) hm0).length_eq
    rw [← hm, List.length_append] at hlen
    have : 1 ≤ (Nat.primeFactorsList (Ideal.absNorm P)).length := by
      have : Nat.primeFactorsList (Ideal.absNorm P) ≠ [] := by
        rw [Ne, Nat.primeFactorsList_eq_nil]; omega
      exact List.length_pos_iff.2 this
    omega
  calc {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard ≤ (↑F : Set (Ideal (𝓞 K))).ncard :=
        Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ ∑ P ∈ T', ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K)
          (n / Ideal.absNorm P)).toFinset.image (P * ·)).card := Finset.card_biUnion_le
    _ ≤ ∑ P ∈ T', (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n / Ideal.absNorm P)).toFinset.card :=
        Finset.sum_le_sum fun P _ => Finset.card_image_le
    _ ≤ ∑ P ∈ T', finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := Finset.sum_le_sum hterm
    _ = T'.card * finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := by simp
    _ ≤ finrank ℚ K * finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) :=
        Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hTcard)
    _ = finrank ℚ K ^ (Nat.primeFactorsList n).length := by
        rw [← pow_succ']; congr 1; omega

/- English proof (translation)
Introduce `K _ _ x hx`. Use `set d := finrank ℚ K`. Establish `hd : 1 ≤ d` using `Module.finrank_pos`. Set `F` to `(Finset.Icc 1 ⌊x⌋₊).biUnion (fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset)`. Establish `hsub : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} ⊆ ↑F`.

Introduce and unpack `I ⟨hI, hx'⟩`. Establish `h0 : Ideal.absNorm I ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Simplify using `only [F, Finset.coe_biUnion, Set.mem_iUnion, Finset.coe_Icc, Set.mem_Icc, Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Conclude with `⟨Ideal.absNorm I, ⟨by omega, Nat.le_floor hx'⟩, rfl⟩`. Use `⟨F.finite_toSet.subset hsub, ?_⟩` and prove the remaining obligations.

Establish `hL : 0 ≤ Real.logb 2 d` using `Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)`. Establish `hx0 : (0:ℝ) < x` using `by linarith`. Establish `h1 : (({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℕ) : ℝ) ≤ (F.card : ℝ)`. Conclude with `(Set.ncard_le_ncard hsub F.finite_toSet).trans (Set.ncard_coe_finset F).le` after adjusting the coercions. Establish `h2 : (F.card : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ideal.finite_setOf_absNorm_eq (S` using `𝓞 K) n).toFinset.card : ℝ) := by`.

Conclude with `Finset.card_biUnion_le` after adjusting the coercions. Establish `h3 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ideal.finite_setOf_absNorm_eq (S` using `𝓞 K) n).toFinset.card : ℝ) ≤ x ^ Real.logb 2 d := by`. Introduce `n hn`. Take `⟨hn1, hn2⟩` from `Finset.mem_Icc.1 hn`. Rewrite using `[← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq _)]`.

Establish `e1 : (({I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) ≤ (d : ℝ) ^ (Nat.primeFactorsList n).length`. Conclude with `normCount_lemma K n hn1` after adjusting the coercions. Establish `e2` using `Formalism.SLP.Final.omegaPow d n hd hn1`. Establish `e3 : (n : ℝ) ^ Real.logb 2 d ≤ x ^ Real.logb 2 d` using `Real.rpow_le_rpow (by positivity) ((Nat.cast_le.2 hn2).trans (Nat.floor_le hx0.le)) hL`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Ideal.finite_setOf_absNorm_eq (S` using `𝓞 K) n).toFinset.card : ℝ) ≤ (⌊x⌋₊ : ℝ) * x ^ Real.logb 2 d := by`. Use `(Finset.sum_le_sum h3).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h5 : (⌊x⌋₊ : ℝ) * x ^ Real.logb 2 d ≤ x * x ^ Real.logb 2 d` using `mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le) (by positivity)`. Rewrite using `[Real.rpow_add hx0, Real.rpow_one]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ideal_norm_le_count : IdealNormLeCount := by
  intro K _ _ x hx
  classical
  set d := finrank ℚ K
  have hd : 1 ≤ d := Module.finrank_pos
  let F := (Finset.Icc 1 ⌊x⌋₊).biUnion (fun n =>
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset)
  have hsub : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} ⊆ ↑F := by
    rintro I ⟨hI, hx'⟩
    have h0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    simp only [F, Finset.coe_biUnion, Set.mem_iUnion, Finset.coe_Icc, Set.mem_Icc,
      Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨Ideal.absNorm I, ⟨by omega, Nat.le_floor hx'⟩, rfl⟩
  refine ⟨F.finite_toSet.subset hsub, ?_⟩
  have hL : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℕ) : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast (Set.ncard_le_ncard hsub F.finite_toSet).trans (Set.ncard_coe_finset F).le
  have h2 : (F.card : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have h3 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.card : ℝ) ≤ x ^ Real.logb 2 d := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    rw [← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq _)]
    have e1 : (({I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) ≤ (d : ℝ) ^ (Nat.primeFactorsList n).length := by
      exact_mod_cast normCount_lemma K n hn1
    have e2 := Formalism.SLP.Final.omegaPow d n hd hn1
    have e3 : (n : ℝ) ^ Real.logb 2 d ≤ x ^ Real.logb 2 d :=
      Real.rpow_le_rpow (by positivity) ((Nat.cast_le.2 hn2).trans (Nat.floor_le hx0.le)) hL
    linarith
  have h4 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.card : ℝ) ≤
      (⌊x⌋₊ : ℝ) * x ^ Real.logb 2 d := by
    refine (Finset.sum_le_sum h3).trans ?_
    simp
  have h5 : (⌊x⌋₊ : ℝ) * x ^ Real.logb 2 d ≤ x * x ^ Real.logb 2 d :=
    mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le) (by positivity)
  rw [Real.rpow_add hx0, Real.rpow_one]
  linarith

/- English proof (translation)
Proceed by induction on `d, hd using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ d hd ih`. Establish `hd' : (0:ℝ) < d` using `by exact_mod_cast hd`. Establish `hinv : (0:ℝ) ≤ 1 / d` using `by positivity`.

Establish `h1 : 1 + (d:ℝ) * (1 / d) ≤ (1 + 1 / d) ^ d` using `one_add_mul_le_pow (by linarith) d`. Establish `h2 : (1:ℝ) + d * (1 / d) = 2` using `by field_simp; ring`. Establish `h3 : ((d:ℝ) + 1) ^ d = (1 + 1 / d) ^ d * (d:ℝ) ^ d`. Rewrite using `[← mul_pow]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Establish `hb : (2:ℝ) * (d:ℝ) ^ d ≤ ((d:ℝ) + 1) ^ d`. Rewrite using `[h3]`. Rewrite `h1` using `[h2]`. Use polynomial arithmetic with `[pow_pos hd' d]`.

Establish `e1 : d + 1 - 1 = (d - 1) + 1` using `by omega`. Rewrite using `[Nat.factorial_succ, e1, pow_succ]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma factorial_mul_two_pow_le_pow (d : ℕ) (hd : 1 ≤ d) : (d.factorial : ℝ) * 2 ^ (d - 1) ≤ (d : ℝ) ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have hd' : (0:ℝ) < d := by exact_mod_cast hd
    have hinv : (0:ℝ) ≤ 1 / d := by positivity
    have h1 : 1 + (d:ℝ) * (1 / d) ≤ (1 + 1 / d) ^ d := one_add_mul_le_pow (by linarith) d
    have h2 : (1:ℝ) + d * (1 / d) = 2 := by field_simp; ring
    have h3 : ((d:ℝ) + 1) ^ d = (1 + 1 / d) ^ d * (d:ℝ) ^ d := by
      rw [← mul_pow]; congr 1; field_simp
    have hb : (2:ℝ) * (d:ℝ) ^ d ≤ ((d:ℝ) + 1) ^ d := by
      rw [h3]; rw [h2] at h1; nlinarith [pow_pos hd' d]
    have e1 : d + 1 - 1 = (d - 1) + 1 := by omega
    rw [Nat.factorial_succ, e1, pow_succ]
    push_cast
    calc ((d:ℝ) + 1) * (d.factorial : ℝ) * (2 ^ (d - 1) * 2)
        = ((d:ℝ) + 1) * 2 * ((d.factorial : ℝ) * 2 ^ (d - 1)) := by ring
      _ ≤ ((d:ℝ) + 1) * 2 * (d:ℝ) ^ d := by gcongr
      _ = ((d:ℝ) + 1) * (2 * (d:ℝ) ^ d) := by ring
      _ ≤ ((d:ℝ) + 1) * ((d:ℝ) + 1) ^ d := by gcongr
      _ = ((d:ℝ) + 1) ^ (d + 1) := by ring

/- English proof (translation)
Introduce `E _ _`. Use `set d := finrank ℚ E`. Establish `hd : 1 ≤ d` using `Module.finrank_pos`. Use `set D : ℝ := |(NumberField.discr E : ℝ)|`. Establish `hD1 : 1 ≤ D`.

Establish `h0` using `NumberField.discr_ne_zero E`. Establish `: (1 : ℤ) ≤ |NumberField.discr E|` using `Int.one_le_abs h0`. Simplify using `only [D]`. Conclude with `this` after adjusting the coercions. Use `set x : ℝ := Real.sqrt D`.

Establish `hx1 : 1 ≤ x` using `by simp only [x]; rw [Real.one_le_sqrt]; exact hD1`. Establish `hr2 : NumberField.InfinitePlace.nrComplexPlaces E ≤ d - 1`. Use `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hc : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E * ((d.factorial : ℝ) / (d : ℝ) ^ d) ≤ 1`.

Establish `hpi : 4 / Real.pi ≤ 2`. Rewrite using `[div_le_iff₀ Real.pi_pos]`. Combine the linear relations using `[Real.pi_gt_three]`. Establish `h1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E ≤ (2:ℝ) ^ (d - 1)` using `(pow_le_pow_left₀ (by positivity) hpi _).trans (pow_le_pow_right₀ (by norm_num) hr2)`. Establish `h2` using `factorial_mul_two_pow_le_pow d hd`.

Establish `hdd : (0:ℝ) < (d:ℝ) ^ d` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Take `⟨hfin, hcount⟩` from `ideal_norm_le_count E x hx1`. Establish `hch : ∀ C : ClassGroup (𝓞 E), ∃ I : (Ideal (𝓞 E))⁰, ClassGroup.mk0 I = C ∧ (Ideal.absNorm (I : Ideal (𝓞 E)) : ℝ) ≤ x`. Introduce `C`.

Take `⟨I, hI, hN⟩` from `NumberField.exists_ideal_in_class_of_norm_le C`. Use `⟨I, hI, hN.trans ?_⟩` and prove the remaining obligations. Establish `hx0 : 0 ≤ x` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `choose f hf1 hf2 using hch`.

Establish `hinj : Function.Injective (fun C => (f C : Ideal (𝓞 E)))`. Introduce `C C' h`. Establish `: f C = f C'` using `Subtype.ext h`. Rewrite using `[← hf1 C, ← hf1 C', this]`. Establish `hcard : NumberField.classNumber E ≤ {I : Ideal (𝓞 E) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard`.

Rewrite using `[Set.ncard_eq_toFinset_card _ hfin]`. Unfold `NumberField.classNumber`. Rewrite using `[← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `I hI`.

Take `⟨C, _, rfl⟩` from `Finset.mem_image.1 hI`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `⟨nonZeroDivisors.coe_ne_zero (f C), hf2 C⟩`. Establish `hxD : x ^ (1 + Real.logb 2 d) = D ^ ((1 + Real.logb 2 d) / 2)`. Simplify using `only [x]`.

Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]`. Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation. Conclude with `hcard` after adjusting the coercions. Use `_ ≤ x ^ (1 + Real.logb 2 d) := hcount`.

Use `_ = D ^ ((1 + Real.logb 2 d) / 2) := hxD`.
-/
theorem class_number_upper_bound : ClassNumberBound := by
  intro E _ _
  classical
  set d := finrank ℚ E
  have hd : 1 ≤ d := Module.finrank_pos
  set D : ℝ := |(NumberField.discr E : ℝ)|
  have hD1 : 1 ≤ D := by
    have h0 := NumberField.discr_ne_zero E
    have : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs h0
    simp only [D]; exact_mod_cast this
  set x : ℝ := Real.sqrt D
  have hx1 : 1 ≤ x := by simp only [x]; rw [Real.one_le_sqrt]; exact hD1

  have hr2 : NumberField.InfinitePlace.nrComplexPlaces E ≤ d - 1 := by
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
    omega
  have hc : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
      ((d.factorial : ℝ) / (d : ℝ) ^ d) ≤ 1 := by
    have hpi : 4 / Real.pi ≤ 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    have h1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E ≤ (2:ℝ) ^ (d - 1) :=
      (pow_le_pow_left₀ (by positivity) hpi _).trans (pow_le_pow_right₀ (by norm_num) hr2)
    have h2 := factorial_mul_two_pow_le_pow d hd
    have hdd : (0:ℝ) < (d:ℝ) ^ d := by positivity
    calc (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
          ((d.factorial : ℝ) / (d : ℝ) ^ d)
        ≤ (2:ℝ) ^ (d - 1) * ((d.factorial : ℝ) / (d : ℝ) ^ d) := by gcongr
      _ = ((d.factorial : ℝ) * 2 ^ (d - 1)) / (d : ℝ) ^ d := by ring
      _ ≤ 1 := by rw [div_le_one hdd]; exact h2
  obtain ⟨hfin, hcount⟩ := ideal_norm_le_count E x hx1

  have hch : ∀ C : ClassGroup (𝓞 E), ∃ I : (Ideal (𝓞 E))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 E)) : ℝ) ≤ x := by
    intro C
    obtain ⟨I, hI, hN⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    refine ⟨I, hI, hN.trans ?_⟩
    have hx0 : 0 ≤ x := by positivity
    calc (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
          ((d.factorial : ℝ) / (d : ℝ) ^ d * x)
        = ((4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
          ((d.factorial : ℝ) / (d : ℝ) ^ d)) * x := by ring
      _ ≤ 1 * x := by gcongr
      _ = x := one_mul x
  choose f hf1 hf2 using hch
  have hinj : Function.Injective (fun C => (f C : Ideal (𝓞 E))) := by
    intro C C' h
    have : f C = f C' := Subtype.ext h
    rw [← hf1 C, ← hf1 C', this]
  have hcard : NumberField.classNumber E ≤
      {I : Ideal (𝓞 E) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    unfold NumberField.classNumber
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro I hI
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.1 hI
    rw [Set.Finite.mem_toFinset]
    exact ⟨nonZeroDivisors.coe_ne_zero (f C), hf2 C⟩
  have hxD : x ^ (1 + Real.logb 2 d) = D ^ ((1 + Real.logb 2 d) / 2) := by
    simp only [x]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    ring_nf
  calc (NumberField.classNumber E : ℝ)
      ≤ (({I : Ideal (𝓞 E) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ x ^ (1 + Real.logb 2 d) := hcount
    _ = D ^ ((1 + Real.logb 2 d) / 2) := hxD

open NumberField Formalism.SLP.P.CountO

/- English proof (translation)
Use `letI : Field (𝓞 E ⧸ p) := Ideal.Quotient.field p`. Establish `hN0 : Ideal.absNorm p ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hNF : Nat.card (𝓞 E ⧸ p) = Ideal.absNorm p`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 E ⧸ p) := Nat.finite_of_card_ne_zero (by rwa [hNF])`.

Use `haveI : Module.Finite (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _`. Use `haveI : Finite (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) := Module.finite_of_finite (𝓞 E ⧸ p)`. Establish `hsm : ∀ (a : 𝓞 E) (q : X ⧸ (p • (⊤ : Submodule (𝓞 E) X))), (Ideal.Quotient.mk p a) • q = a • q`. Introduce `a q`. Rewrite using `[← Ideal.Quotient.algebraMap_eq, algebraMap_smul]`.

Establish `hdim : Module.finrank (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) ≤ k` using `by set b := Module.finBasis (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) choose v hv using fun i => Submodule.Quotient.mk_surjective _ (b i)`. Establish `hli' : LinearIndependent (𝓞 E) v`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i0 hi0`. Assume the negation of the conclusion as `hne`.

Use `set Jg : Ideal (𝓞 E) := Ideal.span (g '' ↑s)`. Establish `hJ0 : Jg ≠ ⊥`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Establish `: g i0 ∈ Jg` using `Ideal.subset_span ⟨i0, hi0, rfl⟩`.

Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot _).1 this`. Establish `hp2 : 2 ≤ Ideal.absNorm p`. Establish `: Ideal.absNorm p ≠ 1` using `by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hp.ne_top`. Use linear arithmetic over natural numbers and integers.

Establish `hex : ∃ e, ¬ Jg ≤ p ^ (e + 1)`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hN : Ideal.absNorm Jg ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Establish `h0` using `Ideal.absNorm_dvd_absNorm_of_le (hall (Ideal.absNorm Jg))`.

Rewrite `h0` using `[map_pow]`. Establish `h1` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h0`. Establish `h2 : Ideal.absNorm Jg < 2 ^ (Ideal.absNorm Jg + 1)` using `(Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))`. Establish `h3 : 2 ^ (Ideal.absNorm Jg + 1) ≤ Ideal.absNorm p ^ (Ideal.absNorm Jg + 1)` using `Nat.pow_le_pow_left hp2 _`. Use linear arithmetic over natural numbers and integers.

Use `set e := Nat.find hex with he_def`. Establish `he1 : ¬ Jg ≤ p ^ (e + 1)` using `Nat.find_spec hex`. Establish `he : Jg ≤ p ^ e`. Break down `Nat.eq_zero_or_pos e with h0 | hpos` into its components or cases. Rewrite using `[h0, pow_zero, Ideal.one_eq_top]`.

Conclude with `le_top`. Use `Nat.find_min hex (show e - 1 < e by omega)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hpos]`. Conclude with `not_not.1 this`. Establish `hpe : p ^ e ≠ ⊥` using `pow_ne_zero e hp0`.

Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hpe`. Take `⟨A, hA⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)`. Establish `hA0 : A ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hA` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hc0 hA`. Establish `hnot : ¬ Jg * A ≤ p ^ (e + 1) * A`. Introduce `h`. Apply `he1` to reduce the goal to its premises. Establish `h' : p ^ (e + 1) * A ∣ Jg * A` using `Ideal.dvd_iff_le.2 h`.

Conclude with `Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hA0).1 h')`. Establish `hgen : ∃ i ∈ s, ∃ x ∈ A, g i * x ∉ p ^ (e + 1) * A`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `hnot` to reduce the goal to its premises.

Establish `hcol : Jg ≤ (p ^ (e + 1) * A).colon A`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `Submodule.mem_colon.2 fun x hx => hall i hi x hx`. Conclude with `Ideal.mul_le.2 fun r hr x hx => Submodule.mem_colon.1 (hcol hr) x hx`.

Take `⟨i1, hi1, x, hx, hnx⟩` from `hgen`. Establish `hy : ∀ i ∈ s, ∃ y : 𝓞 E, y * c = g i * x`. Introduce `i hi`. Establish `: g i * x ∈ Ideal.span {c}`. Rewrite using `[hA]`.

Conclude with `Ideal.mul_mem_mul (he (Ideal.subset_span ⟨i, hi, rfl⟩)) hx`. Conclude with `Ideal.mem_span_singleton'.1 this`. Use `choose! y hy using hy`. Establish `hrel : ∑ i ∈ s, y i • v i = 0`. Apply `htf c hc0` to reduce the goal to its premises.

Rewrite using `[Finset.smul_sum]`. Establish `: ∑ i ∈ s, c • y i • v i = x • ∑ i ∈ s, g i • v i`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, mul_comm c, hy i hi, mul_comm]`.

Rewrite using `[this, hg, smul_zero]`. Establish `hrelQ : ∑ i ∈ s, (Ideal.Quotient.mk p (y i)) • b i = 0`. Use `congrArg (Submodule.mkQ (p • (⊤ : Submodule (𝓞 E) X))) hrel` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, map_smul, Submodule.mkQ_apply, hv]`. Establish `hy1 : Ideal.Quotient.mk p (y i1) = 0` using `linearIndependent_iff'.1 b.linearIndependent s _ hrelQ i1 hi1`. Rewrite `hy1` using `[Ideal.Quotient.eq_zero_iff_mem]`. Apply `hnx` to reduce the goal to its premises.

Rewrite using `[← hy i1 hi1, pow_succ', mul_assoc, ← hA]`. Conclude with `Ideal.mul_mem_mul hy1 (Ideal.mem_span_singleton_self c)`. Simplify using `using hli (Fin _) v hli'`. Establish `hidx : (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index = Ideal.absNorm p ^ Module.finrank (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X)))`. Rewrite using `[← hNF, ← Module.natCard_eq_pow_finrank]`.

Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hidx]`. Conclude with `pow_ne_zero _ hN0`. Rewrite using `[hidx]`.

Conclude with `Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN0) hdim`.
-/
lemma index_ideal_smul_top_le_norm_pow {E : Type} [Field E] [NumberField E] (p : Ideal (𝓞 E)) [hp : p.IsMaximal] (hp0 : p ≠ ⊥)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (k : ℕ) (htf : TF E X)
    (hli : LIB E X k) :
    (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≠ 0 ∧
      (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≤ Ideal.absNorm p ^ k := by
  classical
  letI : Field (𝓞 E ⧸ p) := Ideal.Quotient.field p
  have hN0 : Ideal.absNorm p ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hNF : Nat.card (𝓞 E ⧸ p) = Ideal.absNorm p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ p) := Nat.finite_of_card_ne_zero (by rwa [hNF])
  haveI : Module.Finite (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  haveI : Finite (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) := Module.finite_of_finite (𝓞 E ⧸ p)
  have hsm : ∀ (a : 𝓞 E) (q : X ⧸ (p • (⊤ : Submodule (𝓞 E) X))),
      (Ideal.Quotient.mk p a) • q = a • q := by
    intro a q; rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hdim : Module.finrank (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) ≤ k := by
    set b := Module.finBasis (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X)))
    choose v hv using fun i => Submodule.Quotient.mk_surjective _ (b i)
    have hli' : LinearIndependent (𝓞 E) v := by
      rw [linearIndependent_iff']
      intro s g hg i0 hi0
      by_contra hne
      set Jg : Ideal (𝓞 E) := Ideal.span (g '' ↑s)
      have hJ0 : Jg ≠ ⊥ := by
        intro h; apply hne
        have : g i0 ∈ Jg := Ideal.subset_span ⟨i0, hi0, rfl⟩
        rw [h] at this; exact (Submodule.mem_bot _).1 this
      have hp2 : 2 ≤ Ideal.absNorm p := by
        have : Ideal.absNorm p ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hp.ne_top
        omega
      have hex : ∃ e, ¬ Jg ≤ p ^ (e + 1) := by
        by_contra hall
        push_neg at hall
        have hN : Ideal.absNorm Jg ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
        have h0 := Ideal.absNorm_dvd_absNorm_of_le (hall (Ideal.absNorm Jg))
        rw [map_pow] at h0
        have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h0
        have h2 : Ideal.absNorm Jg < 2 ^ (Ideal.absNorm Jg + 1) :=
          (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
        have h3 : 2 ^ (Ideal.absNorm Jg + 1) ≤ Ideal.absNorm p ^ (Ideal.absNorm Jg + 1) :=
          Nat.pow_le_pow_left hp2 _
        omega
      set e := Nat.find hex with he_def
      have he1 : ¬ Jg ≤ p ^ (e + 1) := Nat.find_spec hex
      have he : Jg ≤ p ^ e := by
        rcases Nat.eq_zero_or_pos e with h0 | hpos
        · rw [h0, pow_zero, Ideal.one_eq_top]; exact le_top
        · have := Nat.find_min hex (show e - 1 < e by omega)
          rw [Nat.sub_add_cancel hpos] at this
          exact not_not.1 this
      have hpe : p ^ e ≠ ⊥ := pow_ne_zero e hp0
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpe
      obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
      have hA0 : A ≠ ⊥ := by
        rintro rfl
        rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hA
        exact hc0 hA
      have hnot : ¬ Jg * A ≤ p ^ (e + 1) * A := by
        intro h
        apply he1
        have h' : p ^ (e + 1) * A ∣ Jg * A := Ideal.dvd_iff_le.2 h
        exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hA0).1 h')
      have hgen : ∃ i ∈ s, ∃ x ∈ A, g i * x ∉ p ^ (e + 1) * A := by
        by_contra hall
        push_neg at hall
        apply hnot
        have hcol : Jg ≤ (p ^ (e + 1) * A).colon A := by
          rw [Ideal.span_le]
          rintro _ ⟨i, hi, rfl⟩
          exact Submodule.mem_colon.2 fun x hx => hall i hi x hx
        exact Ideal.mul_le.2 fun r hr x hx => Submodule.mem_colon.1 (hcol hr) x hx
      obtain ⟨i1, hi1, x, hx, hnx⟩ := hgen
      have hy : ∀ i ∈ s, ∃ y : 𝓞 E, y * c = g i * x := by
        intro i hi
        have : g i * x ∈ Ideal.span {c} := by
          rw [hA]
          exact Ideal.mul_mem_mul (he (Ideal.subset_span ⟨i, hi, rfl⟩)) hx
        exact Ideal.mem_span_singleton'.1 this
      choose! y hy using hy
      have hrel : ∑ i ∈ s, y i • v i = 0 := by
        apply htf c hc0
        rw [Finset.smul_sum]
        have : ∑ i ∈ s, c • y i • v i = x • ∑ i ∈ s, g i • v i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [smul_smul, smul_smul, mul_comm c, hy i hi, mul_comm]
        rw [this, hg, smul_zero]
      have hrelQ : ∑ i ∈ s, (Ideal.Quotient.mk p (y i)) • b i = 0 := by
        have := congrArg (Submodule.mkQ (p • (⊤ : Submodule (𝓞 E) X))) hrel
        rw [map_sum, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsm, map_smul, Submodule.mkQ_apply, hv]
      have hy1 : Ideal.Quotient.mk p (y i1) = 0 :=
        linearIndependent_iff'.1 b.linearIndependent s _ hrelQ i1 hi1
      rw [Ideal.Quotient.eq_zero_iff_mem] at hy1
      apply hnx
      rw [← hy i1 hi1, pow_succ', mul_assoc, ← hA]
      exact Ideal.mul_mem_mul hy1 (Ideal.mem_span_singleton_self c)
    simpa using hli (Fin _) v hli'
  have hidx : (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index =
      Ideal.absNorm p ^ Module.finrank (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) := by
    rw [← hNF, ← Module.natCard_eq_pow_finrank]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hidx]; exact pow_ne_zero _ hN0
  · rw [hidx]; exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN0) hdim

/- English proof (translation)
Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `I hI hN X _ _ _ htf hli`. Distinguish the cases in `htop : I = ⊤`.

Substitute `htop` using the available equality. Rewrite using `[Submodule.top_smul]`. Simplify using the standard rewrite rules. Take `⟨P, hPmax, hIP⟩` from `Ideal.exists_le_maximal I htop`. Take `⟨J, rfl⟩` from `Ideal.dvd_iff_le.2 hIP`.

Establish `hP0 : P ≠ ⊥` using `by rintro rfl; exact hI (Ideal.bot_mul J)`. Establish `hJ0 : J ≠ ⊥` using `by rintro rfl; exact hI (Ideal.mul_bot P)`. Establish `hNP0 : Ideal.absNorm P ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hNP1 : Ideal.absNorm P ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `hPmax.ne_top`. Establish `hNJ0 : Ideal.absNorm J ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Rewrite `hN` using `[map_mul]`. Establish `hlt : Ideal.absNorm J < N`. Rewrite using `[← hN]`.

Establish `: 1 * Ideal.absNorm J < Ideal.absNorm P * Ideal.absNorm J` using `Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hNJ0)`. Use linear arithmetic over natural numbers and integers. Take `⟨hJ1, hJ2⟩` from `ih _ hlt J hJ0 rfl X htf hli`. Use `set L := J • (⊤ : Submodule (𝓞 E) X) with hL`. Take `⟨hU1, hU2⟩` from `index_ideal_smul_top_le_norm_pow P hP0 L k (TF.submodule (h := htf) L) (LIB.submodule (h := hli) L)`.

Establish `hle : P • L ≤ L` using `Submodule.smul_le_right`. Establish `hmul` using `Formalism.SLP.P.CountO.index_comap_mul (P • L) L hle`. Establish `hcomap : (P • L).comap L.subtype = P • (⊤ : Submodule (𝓞 E) L)`. Establish `: (P • (⊤ : Submodule (𝓞 E) L)).map L.subtype = P • L`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]`.

Rewrite using `[← this, Submodule.comap_map_eq_of_injective L.injective_subtype]`. Rewrite `hmul` using `[hcomap]`. Rewrite using `[Submodule.mul_smul, ← hL, ← hmul, map_mul, mul_pow]`. Conclude with `⟨mul_ne_zero hU1 hJ1, Nat.mul_le_mul hU2 hJ2⟩`.
-/
lemma index_ideal_smul_le_norm_pow {E : Type} [Field E] [NumberField E] (k : ℕ) : ∀ (N : ℕ) (I : Ideal (𝓞 E)), I ≠ ⊥ →
    Ideal.absNorm I = N → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
    TF E X → LIB E X k →
    (I • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≠ 0 ∧
      (I • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≤ Ideal.absNorm I ^ k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro I hI hN X _ _ _ htf hli
  by_cases htop : I = ⊤
  · subst htop
    rw [Submodule.top_smul]
    simp
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I htop
  obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hIP
  have hP0 : P ≠ ⊥ := by rintro rfl; exact hI (Ideal.bot_mul J)
  have hJ0 : J ≠ ⊥ := by rintro rfl; exact hI (Ideal.mul_bot P)
  have hNP0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hNP1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPmax.ne_top
  have hNJ0 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [map_mul] at hN
  have hlt : Ideal.absNorm J < N := by
    rw [← hN]
    have : 1 * Ideal.absNorm J < Ideal.absNorm P * Ideal.absNorm J :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hNJ0)
    omega
  obtain ⟨hJ1, hJ2⟩ := ih _ hlt J hJ0 rfl X htf hli
  set L := J • (⊤ : Submodule (𝓞 E) X) with hL
  obtain ⟨hU1, hU2⟩ := index_ideal_smul_top_le_norm_pow P hP0 L k (TF.submodule (h := htf) L) (LIB.submodule (h := hli) L)
  have hle : P • L ≤ L := Submodule.smul_le_right
  have hmul := Formalism.SLP.P.CountO.index_comap_mul (P • L) L hle
  have hcomap : (P • L).comap L.subtype = P • (⊤ : Submodule (𝓞 E) L) := by
    have : (P • (⊤ : Submodule (𝓞 E) L)).map L.subtype = P • L := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← this, Submodule.comap_map_eq_of_injective L.injective_subtype]
  rw [hcomap] at hmul
  rw [Submodule.mul_smul, ← hL, ← hmul, map_mul, mul_pow]
  exact ⟨mul_ne_zero hU1 hJ1, Nat.mul_le_mul hU2 hJ2⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx (fun r hr m _ i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Simplify `I.mul_mem_right (m i) hr` using `[Pi.smul_apply, smul_eq_mul]`. Simplify using `using I.add_mem (ha i) (hb i)`.

Introduce `hx`. Establish `: x = ∑ i, x i • Pi.single i (1 : R)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial`.
-/
lemma mem_ideal_smul_top_pi_iff {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (x : Fin n → R) :
    x ∈ I • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr m _ i => ?_) (fun a b ha hb i => ?_)
    · simpa [Pi.smul_apply, smul_eq_mul] using I.mul_mem_right (m i) hr
    · simpa using I.add_mem (ha i) (hb i)
  · intro hx
    have : x = ∑ i, x i • Pi.single i (1 : R) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.smul_le]`. Introduce `r hr m _`. Conclude with `⟨Submodule.smul_mem_smul hr trivial, Submodule.smul_mem_smul hr trivial⟩`. Introduce and unpack `⟨m, n⟩ ⟨hm, hn⟩`.

Establish `e : ((m, n) : M × N) = LinearMap.inl R M N m + LinearMap.inr R M N n` using `by simp`. Rewrite using `[e]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `: LinearMap.inl R M N m ∈ (I • (⊤ : Submodule R M)).map (LinearMap.inl R M N)` using `Submodule.mem_map_of_mem hm`. Rewrite `this` using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top this`. Establish `: LinearMap.inr R M N n ∈ (I • (⊤ : Submodule R N)).map (LinearMap.inr R M N)` using `Submodule.mem_map_of_mem hn`. Rewrite `this` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top this`.
-/
lemma ideal_smul_top_prod {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (I : Ideal R) :
    I • (⊤ : Submodule R (M × N)) =
      (I • (⊤ : Submodule R M)).prod (I • (⊤ : Submodule R N)) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr m _
    exact ⟨Submodule.smul_mem_smul hr trivial, Submodule.smul_mem_smul hr trivial⟩
  · rintro ⟨m, n⟩ ⟨hm, hn⟩
    have e : ((m, n) : M × N) = LinearMap.inl R M N m + LinearMap.inr R M N n := by simp
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · have : LinearMap.inl R M N m ∈ (I • (⊤ : Submodule R M)).map (LinearMap.inl R M N) :=
        Submodule.mem_map_of_mem hm
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    · have : LinearMap.inr R M N n ∈ (I • (⊤ : Submodule R N)).map (LinearMap.inr R M N) :=
        Submodule.mem_map_of_mem hn
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this

/- English proof (translation)
Introduce `E _ _ P _ _ _ _ I hI`. Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' (𝓞 E) P`. Take `⟨h, hfh⟩` from `Module.projective_lifting_property f (LinearMap.id) hf`. Establish `hfh' : ∀ x, f (h x) = x` using `fun x => LinearMap.congr_fun hfh x`. Use `set Q := LinearMap.ker f with hQ`.

Set `φ : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)` to `h.coprod Q.subtype`. Establish `hφinj : Function.Injective φ`. Introduce and unpack `⟨x, q⟩ ⟨x', q'⟩ hxy`. Simplify using `only [φ, LinearMap.coprod_apply, Submodule.coe_subtype] at hxy`. Establish `h1` using `congrArg f hxy`.

Rewrite `h1` using `[map_add, map_add, hfh', hfh', LinearMap.mem_ker.1 q.2, LinearMap.mem_ker.1 q'.2, add_zero, add_zero]`. Substitute `h1` using the available equality. Conclude with `Prod.ext rfl (Subtype.ext (add_left_cancel hxy))`. Establish `hφsurj : Function.Surjective φ`. Introduce `y`.

Use `⟨(f y, ⟨y - h (f y), ?_⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hfh', sub_self]`. Simplify using `[φ]`. Set `e` to `LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩`. Establish `hhinj : Function.Injective h` using `fun x y hxy => by`.

Rewrite using `[← hfh' x, ← hfh' y, hxy]`. Establish `hpi : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup = AddSubgroup.pi Set.univ (fun _ => (I : Submodule (𝓞 E) (𝓞 E)).toAddSubgroup)`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]`. Conclude with `mem_ideal_smul_top_pi_iff I n x`.

Establish `hfree : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup.index = Ideal.absNorm I ^ n`. Rewrite using `[hpi, AddSubgroup.index_pi]`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `congr 1`. Establish `hcomap : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).comap (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)) = I • ⊤`.

Rewrite using `[Submodule.comap_equiv_eq_map_symm, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]`. Establish `hprod_idx : (I • (⊤ : Submodule (𝓞 E) (P × Q))).toAddSubgroup.index = Ideal.absNorm I ^ n`. Establish `hc : ((I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).comap (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E))).toAddSubgroup = (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup.comap (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)).toAddMonoidHom`. Use extensionality with `x`. Both sides reduce to the same expression.

Rewrite using `[← hcomap, ← hfree, hc]`. Conclude with `AddSubgroup.index_comap_of_surjective _ e.surjective`. Rewrite `hprod_idx` using `[ideal_smul_top_prod]`. Rewrite `hprod_idx` using `[show ((I • (⊤ : Submodule (𝓞 E) P)).prod (I • (⊤ : Submodule (𝓞 E) Q))).toAddSubgroup = (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.prod (I • (⊤ : Submodule (𝓞 E) Q)).toAddSubgroup from rfl, AddSubgroup.index_prod]`. Use `set r := finrank (𝓞 E) P`.

Establish `hTFP : TF E P`. Introduce `a ha x hx`. Establish `: a • h x = 0` using `by rw [← map_smul, hx, map_zero]`. Rewrite `this` using `[smul_eq_zero]`. Break down `this with h0 | h0` into its components or cases.

Conclude with `absurd h0 ha`. Rewrite using `[← hfh' x, h0, map_zero]`. Establish `hTFQ : TF E Q`. Introduce `a ha x hx`. Establish `: a • (x : Fin n → 𝓞 E) = 0` using `by rw [← Submodule.coe_smul, hx, Submodule.coe_zero]`.

Rewrite `this` using `[smul_eq_zero]`. Break down `this with h0 | h0` into its components or cases. Conclude with `absurd h0 ha`. Conclude with `Subtype.ext h0`. Establish `hLIBP : LIB E P r` using `fun ι _ v hv => hv.fintype_card_le_finrank`.

Take `⟨a, ha⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := P) (le_refl r)`. Establish `hrn : r ≤ n`. Use `(ha.map' h (LinearMap.ker_eq_bot.2 hhinj)).fintype_card_le_finrank` as an intermediate fact. Simplify `this` using `[Module.finrank_fin_fun]`. Establish `hLIBQ : LIB E Q (n - r)`.

Introduce `ι _ v hv`. Establish `hc` using `linearIndependent_inl_union_inr' ha hv`. Establish `hc'` using `(hc.map' (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)) (LinearMap.ker_eq_bot.2 e.injective)).fintype_card_le_finrank`. Rewrite `hc'` using `[Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Take `⟨hP1, hP2⟩` from `index_ideal_smul_le_norm_pow (E := E) r _ I hI rfl P hTFP hLIBP`. Take `⟨hQ1, hQ2⟩` from `index_ideal_smul_le_norm_pow (E := E) (n - r) _ I hI rfl Q hTFQ hLIBQ`. Establish `hN : 0 < Ideal.absNorm I` using `Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Express the relevant statement in the definitionally equal form `(I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.index = _`. Assume the negation of the conclusion as `hne`.

Establish `hlt` using `lt_of_le_of_ne hP2 hne`. Establish `hpos : 0 < Ideal.absNorm I ^ (n - r)` using `pow_pos hN _`. Establish `: (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.index * (I • (⊤ : Submodule (𝓞 E) Q)).toAddSubgroup.index < Ideal.absNorm I ^ r * Ideal.absNorm I ^ (n - r)` using `lt_of_le_of_lt (Nat.mul_le_mul_left _ hQ2) (Nat.mul_lt_mul_of_pos_right hlt hpos)`. Rewrite `this` using `[← pow_add, Nat.add_sub_cancel' hrn, hprod_idx]`. Conclude with `lt_irrefl _ this`.
-/
theorem projective_quotient_card : ProjQuotCard := by
  intro E _ _ P _ _ _ _ I hI
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) P
  obtain ⟨h, hfh⟩ := Module.projective_lifting_property f (LinearMap.id) hf
  have hfh' : ∀ x, f (h x) = x := fun x => LinearMap.congr_fun hfh x
  set Q := LinearMap.ker f with hQ
  let φ : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E) := h.coprod Q.subtype
  have hφinj : Function.Injective φ := by
    rintro ⟨x, q⟩ ⟨x', q'⟩ hxy
    simp only [φ, LinearMap.coprod_apply, Submodule.coe_subtype] at hxy
    have h1 := congrArg f hxy
    rw [map_add, map_add, hfh', hfh', LinearMap.mem_ker.1 q.2, LinearMap.mem_ker.1 q'.2,
      add_zero, add_zero] at h1
    subst h1
    exact Prod.ext rfl (Subtype.ext (add_left_cancel hxy))
  have hφsurj : Function.Surjective φ := by
    intro y
    refine ⟨(f y, ⟨y - h (f y), ?_⟩), ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hfh', sub_self]
    · simp [φ]
  let e := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hhinj : Function.Injective h := fun x y hxy => by
    rw [← hfh' x, ← hfh' y, hxy]

  have hpi : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun _ => (I : Submodule (𝓞 E) (𝓞 E)).toAddSubgroup) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    exact mem_ideal_smul_top_pi_iff I n x
  have hfree : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup.index =
      Ideal.absNorm I ^ n := by
    rw [hpi, AddSubgroup.index_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
  have hcomap : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).comap
      (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)) = I • ⊤ := by
    rw [Submodule.comap_equiv_eq_map_symm, Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range]
  have hprod_idx : (I • (⊤ : Submodule (𝓞 E) (P × Q))).toAddSubgroup.index =
      Ideal.absNorm I ^ n := by
    have hc : ((I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).comap
        (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E))).toAddSubgroup =
        (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup.comap
          (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)).toAddMonoidHom := by
      ext x; rfl
    rw [← hcomap, ← hfree, hc]
    exact AddSubgroup.index_comap_of_surjective _ e.surjective
  rw [ideal_smul_top_prod] at hprod_idx
  rw [show ((I • (⊤ : Submodule (𝓞 E) P)).prod (I • (⊤ : Submodule (𝓞 E) Q))).toAddSubgroup =
      (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.prod
        (I • (⊤ : Submodule (𝓞 E) Q)).toAddSubgroup from rfl, AddSubgroup.index_prod] at hprod_idx

  set r := finrank (𝓞 E) P
  have hTFP : TF E P := by
    intro a ha x hx
    have : a • h x = 0 := by rw [← map_smul, hx, map_zero]
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 ha
    · rw [← hfh' x, h0, map_zero]
  have hTFQ : TF E Q := by
    intro a ha x hx
    have : a • (x : Fin n → 𝓞 E) = 0 := by rw [← Submodule.coe_smul, hx, Submodule.coe_zero]
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 ha
    · exact Subtype.ext h0
  have hLIBP : LIB E P r := fun ι _ v hv => hv.fintype_card_le_finrank
  obtain ⟨a, ha⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := P) (le_refl r)
  have hrn : r ≤ n := by
    have := (ha.map' h (LinearMap.ker_eq_bot.2 hhinj)).fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hLIBQ : LIB E Q (n - r) := by
    intro ι _ v hv
    have hc := linearIndependent_inl_union_inr' ha hv
    have hc' := (hc.map' (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E))
      (LinearMap.ker_eq_bot.2 e.injective)).fintype_card_le_finrank
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at hc'
    omega
  obtain ⟨hP1, hP2⟩ := index_ideal_smul_le_norm_pow (E := E) r _ I hI rfl P hTFP hLIBP
  obtain ⟨hQ1, hQ2⟩ := index_ideal_smul_le_norm_pow (E := E) (n - r) _ I hI rfl Q hTFQ hLIBQ
  have hN : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  change (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.index = _
  by_contra hne
  have hlt := lt_of_le_of_ne hP2 hne
  have hpos : 0 < Ideal.absNorm I ^ (n - r) := pow_pos hN _
  have : (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.index *
      (I • (⊤ : Submodule (𝓞 E) Q)).toAddSubgroup.index <
      Ideal.absNorm I ^ r * Ideal.absNorm I ^ (n - r) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hQ2) (Nat.mul_lt_mul_of_pos_right hlt hpos)
  rw [← pow_add, Nat.add_sub_cancel' hrn, hprod_idx] at this
  exact lt_irrefl _ this

end Formalism.HermitianLatticeCounting.P
