import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

open Finset GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EisCong

variable {K : Type} [Field K] [CharZero K]

def pInt (p : ℕ) [Fact p.Prime] (K : Type) [Field K] : Subring K where
  carrier := {x | ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * x)}
  mul_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x * y) = ((D : K) * x) * ((E : K) * y) := by push_cast; ring
    rw [this]; exact hx.mul hy
  one_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x + y) = (E : K) * ((D : K) * x) + (D : K) * ((E : K) * y) := by
      push_cast; ring
    rw [this]
    exact ((isIntegral_natCast E).mul hx).add ((isIntegral_natCast D).mul hy)
  zero_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_zero⟩
  neg_mem' := by
    rintro x ⟨D, hD, hx⟩
    exact ⟨D, hD, by rw [mul_neg]; exact hx.neg⟩

variable {p : ℕ} [Fact p.Prime]

omit [CharZero K] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using h⟩`.
-/
lemma mem_of_isIntegral {x : K} (h : IsIntegral ℤ x) : x ∈ pInt p K :=
  ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using h⟩

/- English proof (translation)
Establish `hm : (m : K) ≠ 0`. Establish `: m ≠ 0` using `by rintro rfl; exact h (dvd_zero _)`. Conclude with `this` after adjusting the coercions. Conclude with `⟨m, h, by rw [mul_inv_cancel₀ hm]; exact isIntegral_one⟩`.
-/
lemma inv_nat_mem {m : ℕ} (h : ¬ p ∣ m) : (m : K)⁻¹ ∈ pInt p K := by
  have hm : (m : K) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; exact h (dvd_zero _)
    exact_mod_cast this
  exact ⟨m, h, by rw [mul_inv_cancel₀ hm]; exact isIntegral_one⟩

/- English proof (translation)
Establish `h1 : ((c.natAbs : ℕ) : K)⁻¹ ∈ pInt p K` using `inv_nat_mem (fun h' => h (Int.natCast_dvd.2 h'))`. Break down `Int.natAbs_eq c with h2 | h2` into its components or cases. Rewrite using `[h2]`. Simplify using `using h1`. Rewrite using `[h2]`.

Simplify using `using neg_mem h1`.
-/
lemma inv_int_mem {c : ℤ} (h : ¬ (p : ℤ) ∣ c) : (c : K)⁻¹ ∈ pInt p K := by
  have h1 : ((c.natAbs : ℕ) : K)⁻¹ ∈ pInt p K := inv_nat_mem (fun h' => h (Int.natCast_dvd.2 h'))
  rcases Int.natAbs_eq c with h2 | h2
  · rw [h2]; simpa using h1
  · rw [h2]; simpa using neg_mem h1

/- English proof (translation)
Break down `e with e | e` into its components or cases. Simplify using `using pow_mem (intCast_mem (pInt p K) c) e`. Rewrite using `[zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem (inv_int_mem h) _`.
-/
lemma zpow_int_mem {c : ℤ} (h : ¬ (p : ℤ) ∣ c) (e : ℤ) : (c : K) ^ e ∈ pInt p K := by
  rcases e with e | e
  · simpa using pow_mem (intCast_mem (pInt p K) c) e
  · rw [zpow_negSucc, ← inv_pow]; exact pow_mem (inv_int_mem h) _

omit [CharZero K] in
/- English proof (translation)
Break down `e with e | e` into its components or cases. Simplify using `using pow_mem (mem_of_isIntegral (h.isIntegral hM)) e`. Rewrite using `[zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem (mem_of_isIntegral (h.inv.isIntegral hM)) _`.
-/
lemma root_zpow_mem {ζ : K} {M : ℕ} (hM : 0 < M) (h : IsPrimitiveRoot ζ M) (e : ℤ) : ζ ^ e ∈ pInt p K := by
  rcases e with e | e
  · simpa using pow_mem (mem_of_isIntegral (h.isIntegral hM)) e
  · rw [zpow_negSucc, ← inv_pow]; exact pow_mem (mem_of_isIntegral (h.inv.isIntegral hM)) _

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Take `⟨v, u, hu, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one`. Establish `hu0 : u ≠ 0` using `by rintro rfl; exact hu (dvd_zero _)`. Establish `hv : v ≤ e`. Establish `: p ^ v < p ^ (e + 1)` using `lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)) h`.

Use `(Nat.pow_lt_pow_iff_right hp.one_lt).1 this` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨w, rfl⟩` from `Nat.exists_eq_add_of_le hv`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `: (p : K) ^ (v + w) / ((p ^ v * u : ℕ) : K) = (p : K) ^ w * (u : K)⁻¹` using `by push_cast; field_simp; ring`.

Rewrite using `[this]`. Conclude with `mul_mem (pow_mem (natCast_mem _ p) w) (inv_nat_mem hu)`.
-/
lemma pow_div_mem {k e : ℕ} (hk : k ≠ 0) (h : k < p ^ (e + 1)) : (p : K) ^ e / k ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hv : v ≤ e := by
    have : p ^ v < p ^ (e + 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)) h
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : K) ^ (v + w) / ((p ^ v * u : ℕ) : K) = (p : K) ^ w * (u : K)⁻¹ := by
    push_cast; field_simp; ring
  rw [this]
  exact mul_mem (pow_mem (natCast_mem _ p) w) (inv_nat_mem hu)

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `h3 : 3 ≤ p` using `by have := hp.two_le; omega`. Establish `h1 : ∀ i : ℕ, i + 2 < 3 ^ (i + 1)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => norm_num`. Consider the case `succ i ih => rw [pow_succ]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : i + 2 < p ^ ((n + 1) * i + 1)` using `(h1 i).trans_le ((Nat.pow_le_pow_left h3 _).trans (Nat.pow_le_pow_right hp.pos (by nlinarith)))`. Use `pow_div_mem (K := K) (k := i + 2) (by omega) h2` as an intermediate fact.

Rewrite using `[← pow_mul]`. Simplify using `using this`.
-/
lemma pow_div_add_two_mem (hp2 : p ≠ 2) (n i : ℕ) : ((p : K) ^ (n + 1)) ^ i / ((i : K) + 2) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h1 : ∀ i : ℕ, i + 2 < 3 ^ (i + 1) := by
    intro i
    induction i with
    | zero => norm_num
    | succ i ih => rw [pow_succ]; omega
  have h2 : i + 2 < p ^ ((n + 1) * i + 1) :=
    (h1 i).trans_le ((Nat.pow_le_pow_left h3 _).trans (Nat.pow_le_pow_right hp.pos (by nlinarith)))
  have := pow_div_mem (K := K) (k := i + 2) (by omega) h2
  rw [← pow_mul]
  simpa using this

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Break down `Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | hodd` into its components or cases. Establish `hk2 : k + 2 = 2 * m` using `by omega`. Take `⟨z, hz⟩` from `Bernoulli.vonStaudt_clausen m`. Establish `hB : bernoulli (k + 2) = (z : ℚ) - ∑ q ∈ Finset.range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q`.

Rewrite using `[hk2, hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hB]`. Use `push_cast`. Rewrite using `[mul_sub, Finset.mul_sum]`.

Use `sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (sum_mem fun q hq => ?_)` and prove the remaining obligations. Establish `hq'` using `(Finset.mem_filter.mp hq).2.1`. Distinguish the cases in `hql : q = p`. Substitute `hql` using the available equality. Establish `: (q : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`.

Rewrite using `[mul_one_div_cancel this]`. Conclude with `one_mem _`. Rewrite using `[one_div]`. Conclude with `mul_mem (natCast_mem _ _) (inv_nat_mem fun h => hql ((Nat.prime_dvd_prime_iff_eq hp hq').mp h).symm)`. Rewrite using `[bernoulli_eq_zero_of_odd hodd (by omega)]`.

Simplify using the standard rewrite rules.
-/
lemma prime_mul_bernoulli_mem (k : ℕ) : (p : K) * ((bernoulli (k + 2) : ℚ) : K) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | hodd
  · have hk2 : k + 2 = 2 * m := by omega
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
    have hB : bernoulli (k + 2) = (z : ℚ) -
        ∑ q ∈ Finset.range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q := by
      rw [hk2, hz]; ring
    rw [hB]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    refine sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (sum_mem fun q hq => ?_)
    have hq' := (Finset.mem_filter.mp hq).2.1
    by_cases hql : q = p
    · subst hql
      have : (q : K) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [mul_one_div_cancel this]; exact one_mem _
    · rw [one_div]
      exact mul_mem (natCast_mem _ _)
        (inv_nat_mem fun h => hql ((Nat.prime_dvd_prime_iff_eq hp hq').mp h).symm)
  · rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    simp

/- English proof (translation)
Establish `h` using `Nat.add_one_mul_choose_eq (m + 1) (i + 1)`. Establish `hi : (i : K) + 2 ≠ 0` using `by exact_mod_cast (show i + 2 ≠ 0 by omega)`. Rewrite using `[eq_div_iff hi]`. Establish `h'` using `congrArg (Nat.cast : ℕ → K) h`. Move the coercions through the operations in `at h'`.

Simplify using `only [add_assoc, one_add_one_eq_two] at h'`. Rewrite using `[← h']`.
-/
lemma choose_cast (m i : ℕ) :
    (((m + 2).choose (i + 2) : ℕ) : K) = ((m : K) + 2) * ((m + 1).choose (i + 1) : ℕ) / ((i : K) + 2) := by
  have h := Nat.add_one_mul_choose_eq (m + 1) (i + 1)
  have hi : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
  rw [eq_div_iff hi]
  have h' := congrArg (Nat.cast : ℕ → K) h
  push_cast at h'
  simp only [add_assoc, one_add_one_eq_two] at h'
  rw [← h']

/- English proof (translation)
Use `set Q : K := (p : K) ^ (n + 1) with hQ`. Use `⟨∑ i ∈ range (m + 1), (t : K) ^ (i + 2) * (x : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) * (Q ^ i / ((i : K) + 2)), sum_mem fun i _ => mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem _ _) _) (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i), ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm (x : K), add_pow, sum_range_succ', sum_range_succ', mul_sum]`. Establish `: ∀ i ∈ range (m + 1), ((t : K) * Q) ^ (i + 1 + 1) * (x : K) ^ (m + 2 - (i + 1 + 1)) * ((m + 2).choose (i + 1 + 1) : ℕ) = ((m : K) + 2) * Q ^ 2 * ((t : K) ^ (i + 2) * (x : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) * (Q ^ i / ((i : K) + 2)))`. Introduce `i _`.

Rewrite using `[show m + 2 - (i + 1 + 1) = m - i by omega, show i + 1 + 1 = i + 2 by omega, choose_cast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_congr rfl this]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma binom_second (hp2 : p ≠ 2) (n m : ℕ) (x t : ℤ) :
    ∃ y ∈ pInt p K, ((x : K) + t * (p : K) ^ (n + 1)) ^ (m + 2) =
      (x : K) ^ (m + 2) + ((m : K) + 2) * t * (p : K) ^ (n + 1) * (x : K) ^ (m + 1) +
        ((m : K) + 2) * ((p : K) ^ (n + 1)) ^ 2 * y := by
  set Q : K := (p : K) ^ (n + 1) with hQ
  refine ⟨∑ i ∈ range (m + 1), (t : K) ^ (i + 2) * (x : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) *
    (Q ^ i / ((i : K) + 2)), sum_mem fun i _ => mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem _ _) _)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i), ?_⟩
  rw [add_comm (x : K), add_pow, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((t : K) * Q) ^ (i + 1 + 1) * (x : K) ^ (m + 2 - (i + 1 + 1)) *
      ((m + 2).choose (i + 1 + 1) : ℕ) = ((m : K) + 2) * Q ^ 2 * ((t : K) ^ (i + 2) * (x : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (Q ^ i / ((i : K) + 2))) := by
    intro i _
    rw [show m + 2 - (i + 1 + 1) = m - i by omega, show i + 1 + 1 = i + 2 by omega, choose_cast]
    ring
  rw [sum_congr rfl this]
  simp
  ring

/- English proof (translation)
Take `⟨y, hy⟩` from `sub_dvd_pow_sub_pow (x + t * Q) x k`. Use `⟨t * y, ?_⟩` and prove the remaining obligations. Use `congrArg (Int.cast : ℤ → K) hy` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Take the linear combination `this`.
-/
lemma binom_first (Q : ℤ) (k : ℕ) (x t : ℤ) :
    ∃ y : ℤ, ((x : K) + t * (Q : K)) ^ k = (x : K) ^ k + Q * y := by
  obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow (x + t * Q) x k
  refine ⟨t * y, ?_⟩
  have := congrArg (Int.cast : ℤ → K) hy
  push_cast at this ⊢
  linear_combination this

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hm : (m : K) + 2 ≠ 0` using `by exact_mod_cast (show m + 2 ≠ 0 by omega)`. Use `⟨∑ i ∈ range (m + 1), ((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (a : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2)), sum_mem fun i _ => mul_mem (mul_mem (mul_mem (prime_mul_bernoulli_mem i) (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _ …` and prove the remaining obligations. Rewrite using `[Polynomial.bernoulli, Polynomial.eval_finsetSum]`.

Simplify using `only [Polynomial.eval_monomial]`. Use `push_cast`. Rewrite using `[sum_div, mul_sum, sum_range_succ', sum_range_succ', mul_sum]`. Establish `: ∀ i ∈ range (m + 1), ((p : K) ^ (n + 1)) ^ (m + 1) * (((bernoulli (i + 1 + 1) : ℚ) : K) * ((m + 2).choose (i + 1 + 1) : ℕ) * ((a : K) / (p : K) ^ (n + 1)) ^ (m + 2 - (i + 1 + 1)) / ((m : K) + 2)) = (p : K) ^ n * (((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (a : K) ^ (m - i) * ( …`. Introduce `i hi`.

Take `⟨l, rfl⟩ : ∃ l, m = i + l` from `⟨m - i, by have := mem_range.1 hi; omega⟩`. Establish `hi2 : (i : K) + 2 ≠ 0` using `by exact_mod_cast (show i + 2 ≠ 0 by omega)`. Rewrite using `[show i + l + 2 - (i + 1 + 1) = l by omega, show i + l - i = l by omega, show i + 1 + 1 = i + 2 by omega, choose_cast, div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[sum_congr rfl this]`. Generalize the expression as in `(∑ i ∈ range (m + 1), _ : K) = S`. Simplify using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma bernoulli_expansion (hp2 : p ≠ 2) (n m : ℕ) (a : ℤ) :
    ∃ y ∈ pInt p K, ((p : K) ^ (n + 1)) ^ (m + 1) *
        (((Polynomial.bernoulli (m + 2)).eval ((a : ℚ) / (p : ℚ) ^ (n + 1)) / ((m + 2 : ℕ) : ℚ) : ℚ) : K) =
      (a : K) ^ (m + 2) / (((m : K) + 2) * (p : K) ^ (n + 1)) - (a : K) ^ (m + 1) / 2 + (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  refine ⟨∑ i ∈ range (m + 1), ((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (a : K) ^ (m - i) *
    ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2)),
    sum_mem fun i _ => mul_mem (mul_mem (mul_mem (prime_mul_bernoulli_mem i)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i), ?_⟩
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  push_cast
  rw [sum_div, mul_sum, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((p : K) ^ (n + 1)) ^ (m + 1) *
      (((bernoulli (i + 1 + 1) : ℚ) : K) * ((m + 2).choose (i + 1 + 1) : ℕ) *
        ((a : K) / (p : K) ^ (n + 1)) ^ (m + 2 - (i + 1 + 1)) / ((m : K) + 2)) =
      (p : K) ^ n * (((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (a : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2))) := by
    intro i hi
    obtain ⟨l, rfl⟩ : ∃ l, m = i + l := ⟨m - i, by have := mem_range.1 hi; omega⟩
    have hi2 : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
    rw [show i + l + 2 - (i + 1 + 1) = l by omega, show i + l - i = l by omega,
      show i + 1 + 1 = i + 2 by omega, choose_cast, div_pow]
    field_simp
    ring
  rw [sum_congr rfl this]
  generalize (∑ i ∈ range (m + 1), _ : K) = S
  simp [div_pow]
  field_simp
  ring

omit [Fact p.Prime] in
/- English proof (translation)
Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Unfold `frc`. Rewrite using `[Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hN)]`. Use `push_cast`. Rewrite using `[mul_div_mul_left _ _ hN']`.
-/
lemma frc_mul {N : ℕ} (hN : 0 < N) (Q : ℕ) (x : ℤ) : frc (N * Q) (N * x) = ((x % (Q : ℤ) : ℤ) : ℚ) / Q := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold frc
  rw [Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hN)]
  push_cast
  rw [mul_div_mul_left _ _ hN']

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hm : (m : K) + 2 ≠ 0` using `by exact_mod_cast (show m + 2 ≠ 0 by omega)`. Establish `hc0 : (c : K) ≠ 0`. Establish `: c ≠ 0` using `by rintro rfl; exact hc (dvd_zero _)`.

Conclude with `this` after adjusting the coercions. Use `set t : ℤ := -(c * α / (p : ℤ) ^ (n + 1)) with ht`. Use `set b : ℤ := c * α + t * (p : ℤ) ^ (n + 1) with hb`. Establish `hb' : (c * α) % (p : ℤ) ^ (n + 1) = b`. Rewrite using `[hb, ht, Int.emod_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `f1 : frc (N * p ^ (n + 1)) (N * α) = (α : ℚ) / (p : ℚ) ^ (n + 1)`. Rewrite using `[frc_mul hN]`. Use `push_cast`. Rewrite using `[Int.emod_eq_of_lt h0 h1]`.

Establish `f2 : frc (N * p ^ (n + 1)) (c * (N * α)) = (b : ℚ) / (p : ℚ) ^ (n + 1)`. Rewrite using `[mul_left_comm, frc_mul hN]`. Use `push_cast`. Rewrite using `[hb']`. Establish `hbK : (b : K) = ((c * α : ℤ) : K) + t * (p : K) ^ (n + 1)` using `by rw [hb]; push_cast; ring`.

Establish `e1 : (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ (N * α) a₂ 0 = (α : K) ^ (m + 1) * (((c : K) ^ 2 - c) / 2 + c * t)`. Break down `h0.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h]`. Simplify using the standard rewrite rules. Establish `hN' : (N : ℤ) ≠ 0` using `by exact_mod_cast hN.ne'`.

Establish `d1 : ¬ ((p : ℤ) ^ (n + 1) ∣ α)` using `fun hd => absurd (Int.le_of_dvd h hd) (not_le.2 h1)`. Establish `d2 : ¬ ((p : ℤ) ^ (n + 1) ∣ c * α)` using `fun hd => d1 <| IsCoprime.dvd_of_dvd_mul_left (IsCoprime.pow_left ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc)) hd`. Establish `d3 : ¬ (((N * p ^ (n + 1) : ℕ) : ℤ) ∣ N * α)` using `by push_cast; rw [mul_dvd_mul_iff_left hN']; exact d1`. Establish `d4 : ¬ (((N * p ^ (n + 1) : ℕ) : ℤ) ∣ c * (N * α))` using `by push_cast; rw [mul_left_comm, mul_dvd_mul_iff_left hN']; exact d2`. Use `congr 1`.

Simplify using `only [smF, eisF, const0, if_true, if_neg d3, if_neg d4, f1, f2]`. Use `push_cast`. Rewrite using `[hbK]`. Use `push_cast`. Evaluate the numerical expressions.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨y1, hy1, E1⟩` from `bernoulli_expansion (K := K) hp2 n m α`. Take `⟨y2, hy2, E2⟩` from `bernoulli_expansion (K := K) hp2 n m b`. Take `⟨y3, hy3, E3⟩` from `binom_second (K := K) hp2 n m (c * α) t`.

Take `⟨y4, E4⟩` from `binom_first (K := K) ((p : ℤ) ^ (n + 1)) (m + 1) (c * α) t`. Rewrite `E3` using `[← hbK]`. Rewrite `E4` using `[Int.cast_pow, Int.cast_natCast, ← hbK]`. Establish `h2 : (2 : K)⁻¹ ∈ pInt p K`. Simplify using `using inv_nat_mem (K := K) (p := p) (m := 2) fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)`.

Establish `hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K)⁻¹) ^ m`. Rewrite using `[show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]`. Establish `hci : ((c : K)⁻¹) ^ m ∈ pInt p K` using `pow_mem (inv_int_mem hc) m`. Use `⟨(c : K) ^ 2 * y1 - ((c : K)⁻¹) ^ m * (y2 + p * y3 - p * y4 * 2⁻¹), sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem hci (sub_mem (add_mem hy2 (mul_mem (natCast_mem _ _) hy3)) (mul_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) h2))), ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Simplify using `only [smF, eisF, const0, if_true, if_neg (show m + 2 ≠ 1 by omega), f1, f2, hz]`. Rewrite `E2` using `[E3, E4]`. Rewrite using `[pow_mul]`. Establish `: ∀ u v A B Q : K, Q * (u * (-A) - v * (-B)) = -(u * (Q * A) - v * (Q * B))` using `by intros; ring`. Rewrite using `[this, E1, E2]`.

Use `push_cast`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma const_congr (hp2 : p ≠ 2) {N : ℕ} (hN : 0 < N) (n m : ℕ) (ζ : K) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    {α : ℤ} (a₂ : ℤ) (h0 : 0 ≤ α) (h1 : α < (p : ℤ) ^ (n + 1)) :
    ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ (N * α) a₂ 0 -
      (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ (N * α) a₂ 0 = (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
    exact_mod_cast this
  set t : ℤ := -(c * α / (p : ℤ) ^ (n + 1)) with ht
  set b : ℤ := c * α + t * (p : ℤ) ^ (n + 1) with hb
  have hb' : (c * α) % (p : ℤ) ^ (n + 1) = b := by
    rw [hb, ht, Int.emod_def]; ring
  have f1 : frc (N * p ^ (n + 1)) (N * α) = (α : ℚ) / (p : ℚ) ^ (n + 1) := by
    rw [frc_mul hN]; push_cast; rw [Int.emod_eq_of_lt h0 h1]
  have f2 : frc (N * p ^ (n + 1)) (c * (N * α)) = (b : ℚ) / (p : ℚ) ^ (n + 1) := by
    rw [mul_left_comm, frc_mul hN]; push_cast; rw [hb']
  have hbK : (b : K) = ((c * α : ℤ) : K) + t * (p : K) ^ (n + 1) := by rw [hb]; push_cast; ring
  have e1 : (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ (N * α) a₂ 0 =
      (α : K) ^ (m + 1) * (((c : K) ^ 2 - c) / 2 + c * t) := by
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have d1 : ¬ ((p : ℤ) ^ (n + 1) ∣ α) := fun hd => absurd (Int.le_of_dvd h hd) (not_le.2 h1)
    have d2 : ¬ ((p : ℤ) ^ (n + 1) ∣ c * α) := fun hd => d1 <|
      IsCoprime.dvd_of_dvd_mul_left (IsCoprime.pow_left
        ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc)) hd
    have d3 : ¬ (((N * p ^ (n + 1) : ℕ) : ℤ) ∣ N * α) := by
      push_cast; rw [mul_dvd_mul_iff_left hN']; exact d1
    have d4 : ¬ (((N * p ^ (n + 1) : ℕ) : ℤ) ∣ c * (N * α)) := by
      push_cast; rw [mul_left_comm, mul_dvd_mul_iff_left hN']; exact d2
    congr 1
    simp only [smF, eisF, const0, if_true, if_neg d3, if_neg d4, f1, f2]
    push_cast
    rw [hbK]
    push_cast
    norm_num
    field_simp
    ring
  obtain ⟨y1, hy1, E1⟩ := bernoulli_expansion (K := K) hp2 n m α
  obtain ⟨y2, hy2, E2⟩ := bernoulli_expansion (K := K) hp2 n m b
  obtain ⟨y3, hy3, E3⟩ := binom_second (K := K) hp2 n m (c * α) t
  obtain ⟨y4, E4⟩ := binom_first (K := K) ((p : ℤ) ^ (n + 1)) (m + 1) (c * α) t
  rw [← hbK] at E3
  rw [Int.cast_pow, Int.cast_natCast, ← hbK] at E4
  have h2 : (2 : K)⁻¹ ∈ pInt p K := by
    simpa using inv_nat_mem (K := K) (p := p) (m := 2)
      fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K)⁻¹) ^ m := by
    rw [show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  have hci : ((c : K)⁻¹) ^ m ∈ pInt p K := pow_mem (inv_int_mem hc) m
  refine ⟨(c : K) ^ 2 * y1 - ((c : K)⁻¹) ^ m * (y2 + p * y3 - p * y4 * 2⁻¹),
    sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem hci (sub_mem (add_mem hy2
      (mul_mem (natCast_mem _ _) hy3)) (mul_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) h2))), ?_⟩
  rw [e1]
  simp only [smF, eisF, const0, if_true, if_neg (show m + 2 ≠ 1 by omega), f1, f2, hz]
  rw [E3, E4] at E2
  rw [pow_mul]
  have : ∀ u v A B Q : K, Q * (u * (-A) - v * (-B)) = -(u * (Q * A) - v * (Q * B)) := by
    intros; ring
  rw [this, E1, E2]
  push_cast
  rw [inv_pow]
  field_simp
  ring

omit [Fact p.Prime] in

/- English proof (translation)
Take `⟨t, ht⟩` from `h.symm.dvd`. Take `⟨y, hy⟩` from `binom_first (K := K) ((p : ℤ) ^ n) k a t`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `hN' : (N : K) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hA : (A : K) = N * a + N * (p : K) ^ n * t`.

Use `congrArg (Int.cast : ℤ → K) ht` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Move the coercions through the operations in `at hy ⊢`. Rewrite using `[← hy, pow_mul, ← mul_pow, hA]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
lemma term_congr (hp0 : (p : K) ≠ 0) {N : ℕ} (hN : 0 < N) (n k : ℕ) {A a : ℤ}
    (h : A ≡ N * a [ZMOD ((N * p ^ n : ℕ) : ℤ)]) :
    ∃ y : ℤ, (p : K) ^ (n * k) * ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k = (a : K) ^ k + (p : K) ^ n * y := by
  obtain ⟨t, ht⟩ := h.symm.dvd
  obtain ⟨y, hy⟩ := binom_first (K := K) ((p : ℤ) ^ n) k a t
  refine ⟨y, ?_⟩
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hA : (A : K) = N * a + N * (p : K) ^ n * t := by
    have := congrArg (Int.cast : ℤ → K) ht
    push_cast at this
    linear_combination this
  push_cast at hy ⊢
  rw [← hy, pow_mul, ← mul_pow, hA]
  congr 1
  field_simp

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hM : 0 < N * p ^ n` using `Nat.mul_pos hN (pow_pos hp.pos n)`. Establish `key : ∀ (A e : ℤ), ∃ y ∈ pInt p K, (a : K) ^ k * (if A ≡ N * a [ZMOD ((N * p ^ n : ℕ) : ℤ)] then ζ ^ e else 0) - (p : K) ^ (n * k) * (if A ≡ N * a [ZMOD ((N * p ^ n : ℕ) : ℤ)] then ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k * ζ ^ e else 0) = (p : K) ^ n * y`. Introduce `A e`.

Use `split_ifs with h`. Take `⟨y, hy⟩` from `term_congr hp0 hN n k h`. Use `⟨-(y * ζ ^ e), neg_mem (mul_mem (intCast_mem _ _) (root_zpow_mem hM hζ e)), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hy]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨0, zero_mem _, by simp⟩`. Use `choose y hy hE using key`. Use `⟨∑ d ∈ r.divisors, (y ((r / d : ℕ) : ℤ) (a₂ * d) - y (-((r / d : ℕ) : ℤ)) (-(a₂ * d))), sum_mem fun d _ => sub_mem (hy _ _) (hy _ _), ?_⟩` and prove the remaining obligations. Unfold `coefPos`. Rewrite using `[mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]`.

Use `sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[mul_sub ((p : K) ^ n), ← hE, ← hE]`. Simplify using `only [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel, Int.cast_neg, Int.cast_natCast, neg_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma coefPos_congr {N : ℕ} (hN : 0 < N) (n k : ℕ) {ζ : K} (hζ : IsPrimitiveRoot ζ (N * p ^ n))
    (a a₂ : ℤ) (r : ℕ) :
    ∃ y ∈ pInt p K, (a : K) ^ k * coefPos 1 (N * p ^ n) ζ (N * a) a₂ r -
      (p : K) ^ (n * k) * coefPos (k + 1) (N * p ^ n) ζ (N * a) a₂ r = (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (pow_pos hp.pos n)
  have key : ∀ (A e : ℤ), ∃ y ∈ pInt p K,
      (a : K) ^ k * (if A ≡ N * a [ZMOD ((N * p ^ n : ℕ) : ℤ)] then ζ ^ e else 0) -
        (p : K) ^ (n * k) * (if A ≡ N * a [ZMOD ((N * p ^ n : ℕ) : ℤ)] then
          ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k * ζ ^ e else 0) = (p : K) ^ n * y := by
    intro A e
    split_ifs with h
    · obtain ⟨y, hy⟩ := term_congr hp0 hN n k h
      refine ⟨-(y * ζ ^ e), neg_mem (mul_mem (intCast_mem _ _) (root_zpow_mem hM hζ e)), ?_⟩
      rw [← mul_assoc, hy]; ring
    · exact ⟨0, zero_mem _, by simp⟩
  choose y hy hE using key
  refine ⟨∑ d ∈ r.divisors, (y ((r / d : ℕ) : ℤ) (a₂ * d) - y (-((r / d : ℕ) : ℤ)) (-(a₂ * d))),
    sum_mem fun d _ => sub_mem (hy _ _) (hy _ _), ?_⟩
  unfold coefPos
  rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sub ((p : K) ^ n), ← hE, ← hE]
  simp only [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel, Int.cast_neg, Int.cast_natCast, neg_div]
  ring

/- English proof (translation)
Introduce `p _ N n j K _ _ ζ hp2 hζ hN _ hj hn c hc α a₂ h0 h1 r`. Establish `hp : p.Prime` using `Fact.out`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Take `⟨m, rfl⟩ : ∃ m, j = m + 2` from `⟨j - 2, by omega⟩`. Choose the witnesses or unpack the hypotheses as in `⟨n, rfl⟩ : ∃ n', n = n' + 1 := by`.

Break down `n with _ | n` into its components or cases. It suffices to derive a contradiction. Use `hp.two_le` as an intermediate fact. Rewrite `hn` using `[pow_zero]`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `⟨n, rfl⟩`. Rewrite using `[show m + 2 - 1 = m + 1 from rfl, Nat.add_sub_cancel]`. It suffices to establish `H : ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ (N * α) a₂ r - (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ (N * α) a₂ r = (p : K) ^ n * y by`. Take `⟨y, ⟨D, hD, hy⟩, E⟩` from `H`. Use `⟨D, hD, ?_⟩` and prove the remaining obligations.

Rewrite using `[E, mul_left_comm, mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]`. Conclude with `hy`. Break down `eq_or_ne r 0 with rfl | hr` into its components or cases. Conclude with `const_congr hp2 hN n m ζ hc a₂ h0 h1`. Establish `hc0 : (c : K) ≠ 0`.

Establish `: c ≠ 0` using `by rintro rfl; exact hc (dvd_zero _)`. Conclude with `this` after adjusting the coercions. Take `⟨y1, hy1, E1⟩` from `coefPos_congr hN (n + 1) (m + 1) hζ α a₂ r`. Take `⟨y2, hy2, E2⟩` from `coefPos_congr hN (n + 1) (m + 1) hζ (c * α) (c * a₂) r`. Establish `hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K)⁻¹) ^ m`.

Rewrite using `[show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]`. Establish `hz1 : (c : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = c` using `by norm_num`. Use `⟨p * ((c : K) ^ 2 * y1 - ((c : K)⁻¹) ^ m * y2), mul_mem (natCast_mem _ _) (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem (pow_mem (inv_int_mem hc) m) hy2)), ?_⟩` and prove the remaining obligations. Simplify using `only [smF, eisF, if_neg hr, hz, hz1]`. Rewrite using `[mul_left_comm c (N : ℤ) α]`.

Establish `hcm : ((c : K)⁻¹) ^ m * ((c * α : ℤ) : K) ^ (m + 1) = c * (α : K) ^ (m + 1)` using `by push_cast; rw [inv_pow]; field_simp; ring`. Take the linear combination `(c : K) ^ 2 * E1 - ((c : K)⁻¹) ^ m * E2 + coefPos 1 (N * p ^ (n + 1)) ζ (N * (c * α)) (c * a₂) r * hcm`.
-/
theorem smF_congr : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ n) → 0 < N → ¬ p ∣ N → 2 ≤ j → j ^ 2 * p ≤ p ^ n → ∀ (c : ℤ), ¬ (p : ℤ) ∣ c → ∀ (α a₂ : ℤ), 0 ≤ α → α < (p : ℤ) ^ n → ∀ r : ℕ, ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * ((α : K) ^ (j - 1) * smF c 1 (N * p ^ n) ζ (N * α) a₂ r - (p : K) ^ (n * (j - 1)) * smF c j (N * p ^ n) ζ (N * α) a₂ r) / (p : K) ^ (n - 1)) := by
  intro p _ N n j K _ _ ζ hp2 hζ hN _ hj hn c hc α a₂ h0 h1 r
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
    rcases n with _ | n
    · exfalso; have := hp.two_le; rw [pow_zero] at hn; nlinarith
    · exact ⟨n, rfl⟩
  rw [show m + 2 - 1 = m + 1 from rfl, Nat.add_sub_cancel]
  suffices H : ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ (N * α) a₂ r -
      (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ (N * α) a₂ r = (p : K) ^ n * y by
    obtain ⟨y, ⟨D, hD, hy⟩, E⟩ := H
    refine ⟨D, hD, ?_⟩
    rw [E, mul_left_comm, mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]
    exact hy
  rcases eq_or_ne r 0 with rfl | hr
  · exact const_congr hp2 hN n m ζ hc a₂ h0 h1
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
    exact_mod_cast this
  obtain ⟨y1, hy1, E1⟩ := coefPos_congr hN (n + 1) (m + 1) hζ α a₂ r
  obtain ⟨y2, hy2, E2⟩ := coefPos_congr hN (n + 1) (m + 1) hζ (c * α) (c * a₂) r
  have hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K)⁻¹) ^ m := by
    rw [show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  have hz1 : (c : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = c := by norm_num
  refine ⟨p * ((c : K) ^ 2 * y1 - ((c : K)⁻¹) ^ m * y2), mul_mem (natCast_mem _ _)
    (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem (pow_mem (inv_int_mem hc) m) hy2)), ?_⟩
  simp only [smF, eisF, if_neg hr, hz, hz1]
  rw [mul_left_comm c (N : ℤ) α]
  have hcm : ((c : K)⁻¹) ^ m * ((c * α : ℤ) : K) ^ (m + 1) = c * (α : K) ^ (m + 1) := by
    push_cast; rw [inv_pow]; field_simp; ring
  linear_combination (c : K) ^ 2 * E1 - ((c : K)⁻¹) ^ m * E2 +
    coefPos 1 (N * p ^ (n + 1)) ζ (N * (c * α)) (c * a₂) r * hcm

end GlobalTheory.EisCong
