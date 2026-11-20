import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[Nat.squarefree_iff_prime_squarefree]`. Introduce `x hx hxx`. Establish `hmem : ∀ t ⊆ s, x ∣ ∏ p ∈ t, p → x ∈ t`. Introduce `t ht hdvd`. Take `⟨p, hp, hxp⟩` from `(Prime.dvd_finset_prod_iff hx.prime _).1 hdvd`.

Rewrite using `[(Nat.prime_dvd_prime_iff_eq hx (h p (ht hp))).1 hxp]`. Conclude with `hp`. Establish `hxs : x ∈ s` using `hmem s subset_rfl (dvd_trans (dvd_mul_right x x) hxx)`. Rewrite `hxx` using `[← Finset.mul_prod_erase s (fun p => p) hxs]`. Use `hmem (s.erase x) (Finset.erase_subset _ _) (Nat.dvd_of_mul_dvd_mul_left hx.pos hxx)` as an intermediate fact.

Simplify using `at this`.
-/
private lemma squarefree_prod_of_prime (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hxx
  have hmem : ∀ t ⊆ s, x ∣ ∏ p ∈ t, p → x ∈ t := by
    intro t ht hdvd
    obtain ⟨p, hp, hxp⟩ := (Prime.dvd_finset_prod_iff hx.prime _).1 hdvd
    rw [(Nat.prime_dvd_prime_iff_eq hx (h p (ht hp))).1 hxp]; exact hp
  have hxs : x ∈ s := hmem s subset_rfl (dvd_trans (dvd_mul_right x x) hxx)
  rw [← Finset.mul_prod_erase s (fun p => p) hxs] at hxx
  have := hmem (s.erase x) (Finset.erase_subset _ _) (Nat.dvd_of_mul_dvd_mul_left hx.pos hxx)
  simp at this

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ hk)]`. Introduce `p`. Rewrite using `[Nat.factorization_pow]`. Distinguish the cases in `hp : p.Prime ∧ p ∣ n`. Establish `h1 : 1 ≤ k.factorization p` using `(hp.1.dvd_iff_one_le_factorization hk).1 (h p hp.1 hp.2)`.

Establish `h2 : n.factorization p < n` using `Nat.factorization_lt p hn`. Simplify using `only [Finsupp.smul_apply, smul_eq_mul]`. Use the polynomial consequences of the given equalities and inequalities. Establish `: n.factorization p = 0`. Distinguish the cases in `hp' : p.Prime`.

Conclude with `Nat.factorization_eq_zero_of_not_dvd (fun hd => hp ⟨hp', hd⟩)`. Conclude with `Nat.factorization_eq_zero_of_not_prime _ hp'`. Rewrite using `[this]`. Conclude with `Nat.zero_le _`.
-/
private lemma dvd_pow_of_prime_dvd_imp (n k : ℕ) (h : ∀ p, p.Prime → p ∣ n → p ∣ k) (hn : n ≠ 0) (hk : k ≠ 0) :
    n ∣ k ^ n := by
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ hk)]
  intro p
  rw [Nat.factorization_pow]
  by_cases hp : p.Prime ∧ p ∣ n
  · have h1 : 1 ≤ k.factorization p := (hp.1.dvd_iff_one_le_factorization hk).1 (h p hp.1 hp.2)
    have h2 : n.factorization p < n := Nat.factorization_lt p hn
    simp only [Finsupp.smul_apply, smul_eq_mul]
    nlinarith
  · have : n.factorization p = 0 := by
      by_cases hp' : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hp ⟨hp', hd⟩)
      · exact Nat.factorization_eq_zero_of_not_prime _ hp'
    rw [this]; exact Nat.zero_le _

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div, ← Nat.sum_div_divisors]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdN` using `Nat.dvd_of_mem_divisors hd`. Establish `hd0 : (d:ℝ) ≠ 0` using `by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'`. Establish `hN0 : (N:ℝ) ≠ 0` using `by exact_mod_cast hN`.

Rewrite using `[Nat.cast_div hdN hd0]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma sum_inv_divisors_eq_sigma_div (N : ℕ) (hN : N ≠ 0) :
    ∑ m ∈ N.divisors, (1 : ℝ) / m = (ArithmeticFunction.sigma 1 N : ℝ) / N := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div, ← Nat.sum_div_divisors]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN := Nat.dvd_of_mem_divisors hd
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast hN
  rw [Nat.cast_div hdN hd0]
  field_simp

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Introduce `n hn`. Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p a hp ha`. Rewrite using `[← pow_mul, ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.totient_prime_pow hp ha]`. Establish `key : (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i = p ^ (a * K + 1) - 1`.

Establish `h1 : 1 ≤ p` using `hp.one_le`. Use `zify [h1, Nat.one_le_pow _ _ hp.pos]`. Rewrite using `[mul_comm, geom_sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_add]`.

Use `congr 1`. Consider the cases of `a with`. Consider the case `zero => omega`. Consider the case `succ a => simp [Nat.succ_sub_one]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (p ^ a) ^ (K + 1) := by rw [← pow_mul]`. Consider the case `zero => exact absurd hn (lt_irrefl 0)`. Consider the case `one => simp`. Consider the case `coprime a b ha hb hab iha ihb`. Rewrite using `[mul_pow, Nat.totient_mul hab, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow K K hab), mul_pow]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma totient_mul_sigma_pow_le_pow_succ (K : ℕ) :
    ∀ n : ℕ, 0 < n → n.totient * ArithmeticFunction.sigma 1 (n ^ K) ≤ n ^ (K + 1) := by
  intro n hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    rw [← pow_mul, ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.totient_prime_pow hp ha]
    have key : (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i = p ^ (a * K + 1) - 1 := by
      have h1 : 1 ≤ p := hp.one_le
      zify [h1, Nat.one_le_pow _ _ hp.pos]
      rw [mul_comm, geom_sum_mul]
    calc p ^ (a - 1) * (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i
        = p ^ (a - 1) * (p ^ (a * K + 1) - 1) := by rw [mul_assoc, key]
      _ ≤ p ^ (a - 1) * p ^ (a * K + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = p ^ (a * (K + 1)) := by
        rw [← pow_add]; congr 1
        cases a with
        | zero => omega
        | succ a => simp [Nat.succ_sub_one]; ring
      _ ≤ (p ^ a) ^ (K + 1) := by rw [← pow_mul]
  | zero => exact absurd hn (lt_irrefl 0)
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [mul_pow, Nat.totient_mul hab,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow K K hab), mul_pow]
    calc a.totient * b.totient * (ArithmeticFunction.sigma 1 (a ^ K) * ArithmeticFunction.sigma 1 (b ^ K))
        = (a.totient * ArithmeticFunction.sigma 1 (a ^ K)) * (b.totient * ArithmeticFunction.sigma 1 (b ^ K)) := by ring
      _ ≤ a ^ (K + 1) * b ^ (K + 1) := Nat.mul_le_mul (iha (by omega)) (ihb (by omega))

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Use `set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD`. Use `set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p with hg`. Establish `hgdvd : ∀ n, g n ∣ n` using `fun n => dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd n)`. Establish `hgD : ∀ n ∈ Finset.Icc 1 Q, g n ∈ D`. Introduce `n hn`.

Rewrite `hn` using `[Finset.mem_Icc]`. Rewrite using `[hD, Finset.mem_filter, Finset.mem_Icc]`. Use `⟨⟨Nat.pos_of_dvd_of_pos (hgdvd n) (by omega), le_trans (Nat.le_of_dvd (by omega) (hgdvd n)) hn.2⟩, squarefree_prod_of_prime _ fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1, Nat.Coprime.prod_left fun p hp => (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_p …` and prove the remaining obligations. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hgD, Finset.mul_sum]`. Use `Finset.sum_le_sum fun f hf => ?_` and prove the remaining obligations.

Rewrite `hf` using `[hD, Finset.mem_filter, Finset.mem_Icc]`. Establish `hf0 : 0 < f` using `hf.1.1`. Establish `hq0 : 0 < q` using `hq`. Use `set N := (f * q) ^ Q with hN`. Establish `hN0 : N ≠ 0` using `pow_ne_zero _ (Nat.mul_pos hf0 hq0).ne'`.

Establish `hfib : ∀ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), f ∣ n ∧ n ∣ N`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_filter, Finset.mem_Icc]`. Use `⟨hn.2 ▸ hgdvd n, dvd_trans (dvd_pow_of_prime_dvd_imp n (f * q) ?_ (by omega) (Nat.mul_pos hf0 hq0).ne') (pow_dvd_pow _ hn.1.2)⟩` and prove the remaining obligations. Introduce `p hp hpn`.

Distinguish the cases in `hpq : p ∣ q`. Conclude with `dvd_mul_of_dvd_right hpq _`. Apply `dvd_mul_of_dvd_left` to reduce the goal to its premises. Rewrite using `[← hn.2]`. Conclude with `Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hp.mem_primeFactors hpn (by omega), hpq⟩)`.

Establish `hf0' : (f:ℝ) ≠ 0` using `by exact_mod_cast hf0.ne'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_image]`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_mul, Nat.mul_div_cancel' (hfib n hn).1]`.

Introduce `x hx y hy hxy`. Conclude with `(Nat.div_left_inj (hfib x hx).1 (hfib y hy).1).1 hxy`. Use `_ ≤ ∑ m ∈ N.divisors, (1:ℝ) / (f * m) := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)` and prove the remaining obligations. Introduce `m hm`.

Take `⟨n, hn, rfl⟩` from `Finset.mem_image.1 hm`. Conclude with `Nat.mem_divisors.2 ⟨dvd_trans (Nat.div_dvd_of_dvd (hfib n hn).1) (hfib n hn).2, hN0⟩`. Use `_ = (1 / f) * ((ArithmeticFunction.sigma 1 N : ℝ) / N) := by`. Rewrite using `[← sum_inv_divisors_eq_sigma_div N hN0, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[one_div_mul_one_div]`. Use `_ ≤ (q:ℝ) / q.totient * (1 / f.totient) := by`. Establish `hcop : Nat.Coprime (f ^ Q) (q ^ Q)` using `Nat.Coprime.pow Q Q hf.2.2`. Rewrite using `[hN, mul_pow, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]`. Establish `hA` using `totient_mul_sigma_pow_le_pow_succ Q f hf0`.

Establish `hB` using `totient_mul_sigma_pow_le_pow_succ Q q hq0`. Establish `hφf : (0:ℝ) < f.totient` using `by exact_mod_cast Nat.totient_pos.2 hf0`. Establish `hφq : (0:ℝ) < q.totient` using `by exact_mod_cast Nat.totient_pos.2 hq0`. Establish `hA' : (f.totient : ℝ) * ArithmeticFunction.sigma 1 (f ^ Q) ≤ (f:ℝ) ^ (Q + 1)` using `by exact_mod_cast hA`. Establish `hB' : (q.totient : ℝ) * ArithmeticFunction.sigma 1 (q ^ Q) ≤ (q:ℝ) ^ (Q + 1)` using `by exact_mod_cast hB`.

Establish `hfpos : (0:ℝ) < f` using `by exact_mod_cast hf0`. Establish `hqpos : (0:ℝ) < q` using `by exact_mod_cast hq0`. Use `push_cast`. Rewrite using `[one_div_mul_eq_div, div_div, div_le_iff₀ (by positivity)]`. Establish `hprod` using `mul_le_mul hA' hB' (by positivity) (by positivity)`.

Establish `hrw : (q:ℝ) / q.totient * (1 / f.totient) * (f ^ Q * q ^ Q * f) = ((f:ℝ) ^ (Q + 1) * (q:ℝ) ^ (Q + 1)) / (q.totient * f.totient)` using `by field_simp; ring`. Rewrite using `[hrw, le_div_iff₀ (by positivity)]`. Use polynomial arithmetic with `[hprod]`.
-/
private lemma sum_inv_le_mul_sum_squarefree_inv_totient (Q q : ℕ) (hq : 1 ≤ q) :
    ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n ≤ ((q:ℝ) / q.totient) *
      ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q), (1:ℝ) / f.totient := by
  set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD
  set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p with hg
  have hgdvd : ∀ n, g n ∣ n := fun n =>
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd n)
  have hgD : ∀ n ∈ Finset.Icc 1 Q, g n ∈ D := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [hD, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.pos_of_dvd_of_pos (hgdvd n) (by omega), le_trans (Nat.le_of_dvd (by omega) (hgdvd n)) hn.2⟩,
      squarefree_prod_of_prime _ fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1,
      Nat.Coprime.prod_left fun p hp => (Nat.Prime.coprime_iff_not_dvd
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).2 (Finset.mem_filter.1 hp).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hgD, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  rw [hD, Finset.mem_filter, Finset.mem_Icc] at hf
  have hf0 : 0 < f := hf.1.1
  have hq0 : 0 < q := hq
  set N := (f * q) ^ Q with hN
  have hN0 : N ≠ 0 := pow_ne_zero _ (Nat.mul_pos hf0 hq0).ne'
  have hfib : ∀ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), f ∣ n ∧ n ∣ N := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨hn.2 ▸ hgdvd n, dvd_trans (dvd_pow_of_prime_dvd_imp n (f * q) ?_ (by omega)
      (Nat.mul_pos hf0 hq0).ne') (pow_dvd_pow _ hn.1.2)⟩
    intro p hp hpn
    by_cases hpq : p ∣ q
    · exact dvd_mul_of_dvd_right hpq _
    · apply dvd_mul_of_dvd_left
      rw [← hn.2]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hp.mem_primeFactors hpn (by omega), hpq⟩)
  have hf0' : (f:ℝ) ≠ 0 := by exact_mod_cast hf0.ne'
  calc ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), (1:ℝ) / n
      = ∑ m ∈ ((Finset.Icc 1 Q).filter (fun n => g n = f)).image (· / f), (1:ℝ) / (f * m) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [← Nat.cast_mul, Nat.mul_div_cancel' (hfib n hn).1]
        · intro x hx y hy hxy
          exact (Nat.div_left_inj (hfib x hx).1 (hfib y hy).1).1 hxy
    _ ≤ ∑ m ∈ N.divisors, (1:ℝ) / (f * m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        exact Nat.mem_divisors.2 ⟨dvd_trans (Nat.div_dvd_of_dvd (hfib n hn).1) (hfib n hn).2, hN0⟩
    _ = (1 / f) * ((ArithmeticFunction.sigma 1 N : ℝ) / N) := by
        rw [← sum_inv_divisors_eq_sigma_div N hN0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ (q:ℝ) / q.totient * (1 / f.totient) := by
        have hcop : Nat.Coprime (f ^ Q) (q ^ Q) := Nat.Coprime.pow Q Q hf.2.2
        rw [hN, mul_pow, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
        have hA := totient_mul_sigma_pow_le_pow_succ Q f hf0
        have hB := totient_mul_sigma_pow_le_pow_succ Q q hq0
        have hφf : (0:ℝ) < f.totient := by exact_mod_cast Nat.totient_pos.2 hf0
        have hφq : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
        have hA' : (f.totient : ℝ) * ArithmeticFunction.sigma 1 (f ^ Q) ≤ (f:ℝ) ^ (Q + 1) := by exact_mod_cast hA
        have hB' : (q.totient : ℝ) * ArithmeticFunction.sigma 1 (q ^ Q) ≤ (q:ℝ) ^ (Q + 1) := by exact_mod_cast hB
        have hfpos : (0:ℝ) < f := by exact_mod_cast hf0
        have hqpos : (0:ℝ) < q := by exact_mod_cast hq0
        push_cast
        rw [one_div_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
        have hprod := mul_le_mul hA' hB' (by positivity) (by positivity)
        have hrw : (q:ℝ) / q.totient * (1 / f.totient) * (f ^ Q * q ^ Q * f)
            = ((f:ℝ) ^ (Q + 1) * (q:ℝ) ^ (Q + 1)) / (q.totient * f.totient) := by
          field_simp; ring
        rw [hrw, le_div_iff₀ (by positivity)]
        nlinarith [hprod]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `h : m % (d * p) + (p * (m / (d * p))) * d = m`. Use `Nat.mod_add_div m (d * p)` as an intermediate fact. Combine the linear relations using `[mul_comm d p, mul_assoc d p (m / (d*p)), mul_comm (p * (m / (d * p))) d]`. Use `conv_rhs => rw [← h]`. Conclude with `(Nat.coprime_add_mul_right_right _ _ _).symm`.
-/
private lemma coprime_mod_mul_iff (d p m : ℕ) : Nat.Coprime d (m % (d * p)) ↔ Nat.Coprime d m := by
  have h : m % (d * p) + (p * (m / (d * p))) * d = m := by
    have := Nat.mod_add_div m (d * p); linarith [mul_comm d p, mul_assoc d p (m / (d*p)), mul_comm (p * (m / (d * p))) d]
  conv_rhs => rw [← h]
  exact (Nat.coprime_add_mul_right_right _ _ _).symm

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]`. Conclude with `⟨fun h => h.1, fun h' => ⟨h', h⟩⟩`.
-/
private lemma coprime_mul_add_mul_iff (d p a b : ℕ) (h : Nat.Coprime d p) :
    Nat.Coprime d (a * p + b * d) ↔ Nat.Coprime d a := by
  rw [Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]
  exact ⟨fun h => h.1, fun h' => ⟨h', h⟩⟩

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hp0` using `hp.pos`. Establish `hcop : Nat.Coprime d p` using `(Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))`. Rewrite using `[← Finset.sum_product']`. Use `symm`. Establish `hmaps : ∀ x ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime), (x.1 * p + x.2 * d) % (d * p) ∈ (Finset.range (d * p)).filter (d * p).Coprime`.

Introduce `x hx`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx ⊢`. Use `⟨Nat.mod_lt _ (Nat.mul_pos hd hp0), Nat.Coprime.mul ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[coprime_mod_mul_iff, coprime_mul_add_mul_iff _ _ _ _ hcop]`. Conclude with `hx.1.2`.

Rewrite using `[mul_comm d p, coprime_mod_mul_iff, add_comm, coprime_mul_add_mul_iff _ _ _ _ hcop.symm]`. Conclude with `hx.2.2`. Establish `hinj : ∀ x ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime), ∀ y ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime), (x.1 * p + x.2 * d) % (d * p) = (y.1 * p + y.2 * d) % (d * p) → x = y`. Introduce `x hx y hy hxy`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx hy`.

Establish `hmod : x.1 * p + x.2 * d ≡ y.1 * p + y.2 * d [MOD d * p]` using `hxy`. Establish `h1 : x.1 * p ≡ y.1 * p [MOD d]`. Use `Nat.ModEq.of_mul_right p hmod` as an intermediate fact. Simplify `this` using `[Nat.ModEq, Nat.add_mul_mod_self_right]`. Establish `h2 : x.2 * d ≡ y.2 * d [MOD p]`.

Use `Nat.ModEq.of_mul_left d hmod` as an intermediate fact. Simplify `this` using `[Nat.ModEq, Nat.add_mul_mod_self_right]`. Establish `e1 : x.1 % d = y.1 % d` using `Nat.ModEq.cancel_right_of_coprime hcop h1`. Establish `e2 : x.2 % p = y.2 % p` using `Nat.ModEq.cancel_right_of_coprime hcop.symm h2`. Rewrite `e1` using `[Nat.mod_eq_of_lt hx.1.1, Nat.mod_eq_of_lt hy.1.1]`.

Rewrite `e2` using `[Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1]`. Conclude with `Prod.ext e1 e2`. Use `Finset.sum_nbij (fun x => (x.1 * p + x.2 * d) % (d * p)) hmaps (fun x hx y hy h => hinj x hx y hy h) ?_ ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨x, hx, hxz⟩` from `Finset.surj_on_of_inj_on_of_card_le (fun x _ => (x.1 * p + x.2 * d) % (d * p)) hmaps (fun x y hx hy h => hinj x hx y hy h) (le_of_eq (by`.

Rewrite using `[Finset.card_product, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime, Nat.totient_mul hcop])) z hz`. Conclude with `⟨x, hx, hxz.symm⟩`. Introduce `x _`. Conclude with `hF _`.
-/
private lemma sum_coprime_range_mul_eq_sum_sum (d p : ℕ) (hd : 0 < d) (hp : p.Prime) (hpd : ¬ p ∣ d)
    (F : ℕ → ℝ) (hF : ∀ m, F m = F (m % (d * p))) :
    ∑ a ∈ (Finset.range (d * p)).filter (d * p).Coprime, F a
      = ∑ a₁ ∈ (Finset.range d).filter d.Coprime, ∑ a₂ ∈ (Finset.range p).filter p.Coprime,
          F (a₁ * p + a₂ * d) := by
  have hp0 := hp.pos
  have hcop : Nat.Coprime d p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))
  rw [← Finset.sum_product']
  symm
  have hmaps : ∀ x ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime),
      (x.1 * p + x.2 * d) % (d * p) ∈ (Finset.range (d * p)).filter (d * p).Coprime := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hd hp0), Nat.Coprime.mul ?_ ?_⟩
    · rw [coprime_mod_mul_iff, coprime_mul_add_mul_iff _ _ _ _ hcop]; exact hx.1.2
    · rw [mul_comm d p, coprime_mod_mul_iff, add_comm, coprime_mul_add_mul_iff _ _ _ _ hcop.symm]
      exact hx.2.2
  have hinj : ∀ x ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime),
      ∀ y ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime),
      (x.1 * p + x.2 * d) % (d * p) = (y.1 * p + y.2 * d) % (d * p) → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx hy
    have hmod : x.1 * p + x.2 * d ≡ y.1 * p + y.2 * d [MOD d * p] := hxy
    have h1 : x.1 * p ≡ y.1 * p [MOD d] := by
      have := Nat.ModEq.of_mul_right p hmod
      simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using this
    have h2 : x.2 * d ≡ y.2 * d [MOD p] := by
      have := Nat.ModEq.of_mul_left d hmod
      simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using this
    have e1 : x.1 % d = y.1 % d := Nat.ModEq.cancel_right_of_coprime hcop h1
    have e2 : x.2 % p = y.2 % p := Nat.ModEq.cancel_right_of_coprime hcop.symm h2
    rw [Nat.mod_eq_of_lt hx.1.1, Nat.mod_eq_of_lt hy.1.1] at e1
    rw [Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1] at e2
    exact Prod.ext e1 e2
  refine Finset.sum_nbij (fun x => (x.1 * p + x.2 * d) % (d * p)) hmaps (fun x hx y hy h => hinj x hx y hy h) ?_ ?_
  · intro z hz
    obtain ⟨x, hx, hxz⟩ := Finset.surj_on_of_inj_on_of_card_le
      (fun x _ => (x.1 * p + x.2 * d) % (d * p)) hmaps (fun x y hx hy h => hinj x hx y hy h) (le_of_eq (by
        rw [Finset.card_product, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime,
          ← Nat.totient_eq_card_coprime, Nat.totient_mul hcop])) z hz
    exact ⟨x, hx, hxz.symm⟩
  · intro x _; exact hF _

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Establish `hD' : (D:ℂ) ≠ 0` using `by exact_mod_cast hD.ne'`. Establish `h` using `Nat.div_add_mod m D`. Establish `: (m:ℂ) = D * (m / D : ℕ) + (m % D : ℕ)` using `by exact_mod_cast h.symm`. Generalize the expression as in `m / D = k at this`.

Use `⟨(n * k : ℕ), ?_⟩` and prove the remaining obligations. Rewrite using `[this]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma cexp_mul_div_eq_of_mod_right (D : ℕ) (hD : 0 < D) (n m : ℕ) :
    cexp (2 * ↑Real.pi * I * n * m / D) = cexp (2 * ↑Real.pi * I * n * ↑(m % D) / D) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hD' : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have h := Nat.div_add_mod m D
  have : (m:ℂ) = D * (m / D : ℕ) + (m % D : ℕ) := by exact_mod_cast h.symm
  generalize m / D = k at this
  refine ⟨(n * k : ℕ), ?_⟩
  rw [this]; push_cast; field_simp; ring

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Establish `hd' : (d:ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hp' : (p:ℂ) ≠ 0` using `by exact_mod_cast hp.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma cexp_crt_combination_eq_mul (d p n a₁ a₂ : ℕ) (hd : 0 < d) (hp : 0 < p) :
    cexp (2 * ↑Real.pi * I * n * ↑(a₁ * p + a₂ * d) / ↑(d * p))
      = cexp (2 * ↑Real.pi * I * n * a₁ / d) * cexp (2 * ↑Real.pi * I * n * a₂ / p) := by
  rw [← Complex.exp_add]
  congr 1
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h1⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Simplify using `[Nat.coprime_zero_right] at h2`. Conclude with `hp.one_lt.ne' h2`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h2, (Nat.Prime.coprime_iff_not_dvd hp).2 ?_⟩` and prove the remaining obligations.

Introduce `h`. Conclude with `h1 (Nat.eq_zero_of_dvd_of_lt h h2)`.
-/
private lemma filter_coprime_range_prime_eq_erase_zero (p : ℕ) (hp : p.Prime) :
    (Finset.range p).filter p.Coprime = (Finset.range p).erase 0 := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rintro rfl
    simp [Nat.coprime_zero_right] at h2
    exact hp.one_lt.ne' h2
  · rintro ⟨h1, h2⟩
    refine ⟨h2, (Nat.Prime.coprime_iff_not_dvd hp).2 ?_⟩
    intro h
    exact h1 (Nat.eq_zero_of_dvd_of_lt h h2)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Establish `hd' : (d:ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `h` using `Nat.div_add_mod n d`. Establish `: (n:ℂ) = d * (n / d : ℕ) + (n % d : ℕ)` using `by exact_mod_cast h.symm`. Generalize the expression as in `n / d = m at this`.

Use `⟨(m * a : ℕ), ?_⟩` and prove the remaining obligations. Rewrite using `[this]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma cexp_mul_div_eq_natMod_left (d : ℕ) (hd : 0 < d) (n a : ℕ) :
    cexp (2 * ↑Real.pi * I * n * a / d) = cexp (2 * ↑Real.pi * I * ↑(n % d) * a / d) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := Nat.div_add_mod n d
  have : (n:ℂ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast h.symm
  generalize n / d = m at this
  refine ⟨(m * a : ℕ), ?_⟩
  rw [this]; push_cast; field_simp; ring

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hd' : (d:ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Use `set ζ := cexp (2 * ↑Real.pi * I * k / d) with hζ`. Establish `hterm : ∀ a : ℕ, cexp (2 * ↑Real.pi * I * k * a / d) = ζ ^ a`. Introduce `a`. Rewrite using `[hζ, ← Complex.exp_nat_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hterm]`. Establish `hζd : ζ ^ d = 1`. Rewrite using `[hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`.

Conclude with `⟨k, by field_simp⟩`. Use `split_ifs with h`. Take `⟨j, rfl⟩` from `h`. Establish `: ζ = 1`. Rewrite using `[hζ, Complex.exp_eq_one_iff]; exact ⟨j, by push_cast; field_simp⟩`.

Simplify using `[this]`. Establish `hne : ζ ≠ 1`. Introduce `h1`. Rewrite `h1` using `[hζ, Complex.exp_eq_one_iff]`. Take `⟨j, hj⟩` from `h1`.

Apply `h` to reduce the goal to its premises. Use `⟨j, ?_⟩` and prove the remaining obligations. Clear denominators, using `at hj` for the nonvanishing conditions. Conclude with `hj` after adjusting the coercions. Rewrite using `[geom_sum_eq hne, hζd, sub_self, zero_div]`.
-/
private lemma sum_range_cexp_eq_ite_dvd (d : ℕ) (hd : 0 < d) (k : ℤ) :
    ∑ a ∈ Finset.range d, cexp (2 * ↑Real.pi * I * k * a / d) = if (d:ℤ) ∣ k then (d:ℂ) else 0 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set ζ := cexp (2 * ↑Real.pi * I * k / d) with hζ
  have hterm : ∀ a : ℕ, cexp (2 * ↑Real.pi * I * k * a / d) = ζ ^ a := by
    intro a; rw [hζ, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hterm]
  have hζd : ζ ^ d = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨k, by field_simp⟩
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : ζ = 1 := by
      rw [hζ, Complex.exp_eq_one_iff]; exact ⟨j, by push_cast; field_simp⟩
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨j, hj⟩ := h1
      apply h
      refine ⟨j, ?_⟩
      field_simp at hj
      exact_mod_cast hj
    rw [geom_sum_eq hne, hζd, sub_self, zero_div]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Use `set B : ℕ → ℂ := fun r => ∑ n ∈ S.filter (fun n => n % d = r), b n with hB`. Establish `hgroup : ∀ a : ℕ, ∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d) = ∑ r ∈ Finset.range d, B r * cexp (2 * ↑Real.pi * I * r * a / d)`. Introduce `a`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := fun n => n % d) (t := Finset.range d) (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hd))]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[hB, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite using `[cexp_mul_div_eq_natMod_left d hd n a, (Finset.mem_filter.1 hn).2]`. Establish `hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * (starRingEnd ℂ) z`. Introduce `z`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `clear_value B`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[hgroup, hsq, map_sum, map_mul, Finset.sum_mul_sum]`. Establish `horth : ∀ r ∈ Finset.range d, ∀ s ∈ Finset.range d, ∑ a ∈ Finset.range d, B r * cexp (2 * ↑Real.pi * I * r * a / d) * ((starRingEnd ℂ) (B s) * (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * s * a / d))) = if r = s then d * (B r * (starRingEnd ℂ) (B s)) else 0`. Introduce `r hr s hs`.

Establish `hconj : ∀ a : ℕ, cexp (2 * ↑Real.pi * I * r * a / d) * (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * s * a / d)) = cexp (2 * ↑Real.pi * I * ((r:ℤ) - s : ℤ) * a / d)`. Introduce `a`. Rewrite using `[← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← hconj a]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[sum_range_cexp_eq_ite_dvd d hd]`. Establish `hr'` using `Finset.mem_range.1 hr`.

Establish `hs'` using `Finset.mem_range.1 hs`. Distinguish the cases in `hrs : r = s`. Substitute `hrs` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish `: ¬ (d:ℤ) ∣ ((r:ℤ) - s)`. Introduce `⟨j, hj⟩`. Apply `hrs` to reduce the goal to its premises. Establish `h1 : (r:ℤ) - s < d` using `by omega`. Establish `h2 : -(d:ℤ) < (r:ℤ) - s` using `by omega`.

Establish `: j = 0`. Break down `lt_trichotomy j 0 with h | h | h` into its components or cases. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h`. Use the polynomial consequences of the given equalities and inequalities.

Substitute `this` using the available equality. Use linear arithmetic over natural numbers and integers. Simplify using `[this, hrs]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl fun s hs => horth r hr s hs, Finset.sum_ite_eq]`. Simplify using `only [hr, if_true]`. Rewrite using `[hB]`. Simplify using `[map_sum, Finset.sum_mul_sum]`.
-/
private lemma sum_norm_sq_exp_sum_eq_mul_sum_residues (d : ℕ) (hd : 0 < d) (S : Finset ℕ) (b : ℕ → ℂ) :
    ∑ a ∈ Finset.range d, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2
      = d * ∑ r ∈ Finset.range d, ‖∑ n ∈ S.filter (fun n => n % d = r), b n‖ ^ 2 := by
  set B : ℕ → ℂ := fun r => ∑ n ∈ S.filter (fun n => n % d = r), b n with hB
  have hgroup : ∀ a : ℕ, ∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)
      = ∑ r ∈ Finset.range d, B r * cexp (2 * ↑Real.pi * I * r * a / d) := by
    intro a
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % d) (t := Finset.range d)
      (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hd))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hB, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [cexp_mul_div_eq_natMod_left d hd n a, (Finset.mem_filter.1 hn).2]
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  clear_value B
  apply Complex.ofReal_injective
  push_cast
  rw [Finset.mul_sum]
  simp_rw [hgroup, hsq, map_sum, map_mul, Finset.sum_mul_sum]
  have horth : ∀ r ∈ Finset.range d, ∀ s ∈ Finset.range d,
      ∑ a ∈ Finset.range d, B r * cexp (2 * ↑Real.pi * I * r * a / d) *
        ((starRingEnd ℂ) (B s) * (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * s * a / d)))
        = if r = s then d * (B r * (starRingEnd ℂ) (B s)) else 0 := by
    intro r hr s hs
    have hconj : ∀ a : ℕ, cexp (2 * ↑Real.pi * I * r * a / d) * (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * s * a / d))
        = cexp (2 * ↑Real.pi * I * ((r:ℤ) - s : ℤ) * a / d) := by
      intro a
      rw [← Complex.exp_conj, ← Complex.exp_add]; congr 1
      simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
      push_cast; ring
    calc _ = B r * (starRingEnd ℂ) (B s) * ∑ a ∈ Finset.range d, cexp (2 * ↑Real.pi * I * ((r:ℤ) - s : ℤ) * a / d) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; rw [← hconj a]; ring
      _ = _ := by
          rw [sum_range_cexp_eq_ite_dvd d hd]
          have hr' := Finset.mem_range.1 hr; have hs' := Finset.mem_range.1 hs
          by_cases hrs : r = s
          · subst hrs; simp; ring
          · have : ¬ (d:ℤ) ∣ ((r:ℤ) - s) := by
              intro ⟨j, hj⟩
              apply hrs
              have h1 : (r:ℤ) - s < d := by omega
              have h2 : -(d:ℤ) < (r:ℤ) - s := by omega
              have : j = 0 := by
                rcases lt_trichotomy j 0 with h | h | h
                · nlinarith
                · exact h
                · nlinarith
              subst this; omega
            simp [this, hrs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s hs => horth r hr s hs, Finset.sum_ite_eq]
  simp only [hr, if_true]
  rw [hB]
  simp [map_sum, Finset.sum_mul_sum]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Establish `hp0` using `hp.pos`. Establish `hpar` using `sum_norm_sq_exp_sum_eq_mul_sum_residues p hp0 S b`. Rewrite `hpar` using `[← Finset.add_sum_erase _ _ (Finset.mem_range.2 hp0)]`. Simplify using `only [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at hpar`. Use `set B : ℕ → ℝ := fun r => ‖∑ n ∈ S.filter (fun n => n % p = r), b n‖ with hB`.

Establish `hc : B (c % p) = 0`. Simplify using `only [hB, norm_eq_zero]`. Rewrite using `[Finset.filter_false_of_mem]`. Use the proof step `· simp`. Introduce `n hn h`.

Conclude with `hS n hn h`. Establish `hsplit : ∑ n ∈ S, b n = ∑ r ∈ ((Finset.range p).erase (c % p)), ∑ n ∈ S.filter (fun n => n % p = r), b n`. Rewrite using `[Finset.sum_erase]`. Conclude with `(Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := Finset.range p) (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hp0)) b).symm`. Rewrite using `[← norm_eq_zero]`.

Conclude with `hc`. Establish `hcs : ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ r ∈ Finset.range p, B r ^ 2`. Rewrite using `[hsplit]`. Establish `hcard : (((Finset.range p).erase (c % p)).card : ℝ) = p - 1`. Rewrite using `[Finset.card_erase_of_mem (Finset.mem_range.2 (Nat.mod_lt c hp0)), Finset.card_range]`.

Move the coercions through the operations in `[Nat.cast_sub hp.one_le]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcard]`. Use `gcongr`.

Establish `: (1:ℝ) ≤ p` using `by exact_mod_cast hp.one_le`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Finset.erase_subset _ _`. Establish `hp1 : (1:ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hB' : ∑ r ∈ Finset.range p, B r ^ 2 = ∑ r ∈ Finset.range p, ‖∑ n ∈ S.filter (fun n => n % p = r), b n‖ ^ 2` using `rfl`.

Rewrite `hpar` using `[← hB']`. Use polynomial arithmetic with `[hcs, hpar, sq_nonneg ‖∑ n ∈ S, b n‖]`.
-/
private lemma norm_sum_sq_le_pred_mul_of_avoids_class (p : ℕ) (hp : p.Prime) (c : ℕ) (S : Finset ℕ) (b : ℕ → ℂ)
    (hS : ∀ n ∈ S, ¬ n ≡ c [MOD p]) :
    ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) *
      ∑ a ∈ (Finset.range p).erase 0, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p)‖ ^ 2 := by
  have hp0 := hp.pos
  have hpar := sum_norm_sq_exp_sum_eq_mul_sum_residues p hp0 S b
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hp0)] at hpar
  simp only [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at hpar
  set B : ℕ → ℝ := fun r => ‖∑ n ∈ S.filter (fun n => n % p = r), b n‖ with hB
  have hc : B (c % p) = 0 := by
    simp only [hB, norm_eq_zero]
    rw [Finset.filter_false_of_mem]; · simp
    intro n hn h; exact hS n hn h
  have hsplit : ∑ n ∈ S, b n = ∑ r ∈ ((Finset.range p).erase (c % p)), ∑ n ∈ S.filter (fun n => n % p = r), b n := by
    rw [Finset.sum_erase]
    · exact (Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := Finset.range p)
        (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hp0)) b).symm
    · rw [← norm_eq_zero]; exact hc
  have hcs : ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ r ∈ Finset.range p, B r ^ 2 := by
    rw [hsplit]
    have hcard : (((Finset.range p).erase (c % p)).card : ℝ) = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 (Nat.mod_lt c hp0)), Finset.card_range]
      push_cast [Nat.cast_sub hp.one_le]; ring
    calc _ ≤ (∑ r ∈ (Finset.range p).erase (c % p), B r) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (((Finset.range p).erase (c % p)).card : ℝ) * ∑ r ∈ (Finset.range p).erase (c % p), B r ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (p - 1 : ℝ) * ∑ r ∈ Finset.range p, B r ^ 2 := by
          rw [hcard]
          gcongr
          · have : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
            linarith
          · exact Finset.erase_subset _ _
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hB' : ∑ r ∈ Finset.range p, B r ^ 2 = ∑ r ∈ Finset.range p, ‖∑ n ∈ S.filter (fun n => n % p = r), b n‖ ^ 2 := rfl
  rw [← hB'] at hpar
  nlinarith [hcs, hpar, sq_nonneg ‖∑ n ∈ S, b n‖]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
/- English proof (translation)
Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `hd hsq hcl b`. Distinguish the cases in `h1 : d = 1`.

Substitute `h1` using the available equality. Establish `: (Finset.range 1).filter (Nat.Coprime 1) = {0}` using `by decide`. Simplify using `[this]`. Take `⟨p, hp, hpd⟩` from `Nat.exists_prime_and_dvd h1`. Take `⟨d₁, rfl⟩` from `hpd`.

Rewrite `hsq`, `hcl`, the goal using `[mul_comm p d₁]`. Establish `hd₁ : 0 < d₁` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hd)`. Establish `hpd₁ : ¬ p ∣ d₁`. Introduce `h`. Use `hsq p (Nat.mul_dvd_mul h (dvd_refl p))` as an intermediate fact.

Conclude with `hp.one_lt.ne' (Nat.isUnit_iff.1 this)`. Establish `hlt : d₁ < d₁ * p` using `lt_mul_of_one_lt_right hd₁ hp.one_lt`. Establish `ih'` using `ih d₁ (by rw [mul_comm]; exact hlt) hd₁ (hsq.squarefree_of_dvd (dvd_mul_right _ _)) (fun q hq hqd => hcl q hq (dvd_mul_of_dvd_left hqd _))`. Take `⟨c, hc⟩` from `hcl p hp (dvd_mul_left _ _)`. Establish `hcop : Nat.Coprime d₁ p` using `(Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd₁))`.

Rewrite using `[sum_coprime_range_mul_eq_sum_sum d₁ p hd₁ hp hpd₁ (fun m => ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * m / ↑(d₁ * p))‖ ^ 2) (fun m => by`. Use `congr 2`. Conclude with `Finset.sum_congr rfl fun n _ => by rw [cexp_mul_div_eq_of_mod_right _ (Nat.mul_pos hd₁ hp.pos) n m])]`. Repeatedly rewrite using `[cexp_crt_combination_eq_mul d₁ p _ _ _ hd₁ hp.pos, filter_coprime_range_prime_eq_erase_zero p hp, Nat.totient_mul hcop, Nat.totient_prime hp]`. Establish `hstep : ∀ a₁ : ℕ, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ a₂ ∈ (Finset.range p).erase 0, ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2`.

Introduce `a₁`. Use `norm_sum_sq_le_pred_mul_of_avoids_class p hp c S (fun n => b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)) hc` as an intermediate fact. Simplify `this` using `only [mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum]`.

Move the coercions through the operations in `[Nat.cast_sub hp.one_le]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma norm_sum_sq_le_totient_mul_of_avoids_classes (S : Finset ℕ) :
    ∀ d : ℕ, 0 < d → Squarefree d → (∀ p : ℕ, p.Prime → p ∣ d → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) →
    ∀ b : ℕ → ℂ, ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d.totient : ℝ) *
      ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hsq hcl b
  by_cases h1 : d = 1
  · subst h1
    have : (Finset.range 1).filter (Nat.Coprime 1) = {0} := by decide
    simp [this]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨d₁, rfl⟩ := hpd
  rw [mul_comm p d₁] at hsq hcl ⊢
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
  have hpd₁ : ¬ p ∣ d₁ := by
    intro h
    have := hsq p (Nat.mul_dvd_mul h (dvd_refl p))
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hlt : d₁ < d₁ * p := lt_mul_of_one_lt_right hd₁ hp.one_lt
  have ih' := ih d₁ (by rw [mul_comm]; exact hlt) hd₁ (hsq.squarefree_of_dvd (dvd_mul_right _ _))
    (fun q hq hqd => hcl q hq (dvd_mul_of_dvd_left hqd _))
  obtain ⟨c, hc⟩ := hcl p hp (dvd_mul_left _ _)
  have hcop : Nat.Coprime d₁ p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd₁))
  rw [sum_coprime_range_mul_eq_sum_sum d₁ p hd₁ hp hpd₁
    (fun m => ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * m / ↑(d₁ * p))‖ ^ 2)
    (fun m => by
      congr 2
      exact Finset.sum_congr rfl fun n _ => by rw [cexp_mul_div_eq_of_mod_right _ (Nat.mul_pos hd₁ hp.pos) n m])]
  simp_rw [cexp_crt_combination_eq_mul d₁ p _ _ _ hd₁ hp.pos, filter_coprime_range_prime_eq_erase_zero p hp, Nat.totient_mul hcop,
    Nat.totient_prime hp]
  have hstep : ∀ a₁ : ℕ, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 ≤ (p - 1 : ℝ) *
      ∑ a₂ ∈ (Finset.range p).erase 0,
        ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2 := by
    intro a₁
    have := norm_sum_sq_le_pred_mul_of_avoids_class p hp c S (fun n => b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)) hc
    simpa only [mul_assoc] using this
  calc ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime,
        ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 := ih' b
    _ ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, (p - 1 : ℝ) *
        ∑ a₂ ∈ (Finset.range p).erase 0,
        ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2 := by
        gcongr with a₁ _; exact hstep a₁
    _ = _ := by
        rw [← Finset.mul_sum]; push_cast [Nat.cast_sub hp.one_le]; ring

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in

/- English proof (translation)
Introduce `M N Q q S hQ hq hS hcl`. Use `set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD`. Use `set Z : ℝ := (S.card : ℝ) with hZ`. Establish `hZ0 : 0 ≤ Z` using `Nat.cast_nonneg _`. Establish `hRHS : 0 ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N` using `by positivity`.

Establish `hφq : (0:ℝ) < q.totient` using `by exact_mod_cast Nat.totient_pos.2 hq`. Establish `hqpos : (0:ℝ) < q` using `by exact_mod_cast hq`. Establish `hlog : Real.log Q ≤ ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n`. Establish `h1` using `log_add_one_le_harmonic Q`. Rewrite `h1` using `[harmonic_eq_sum_Icc]`.

Move the coercions through the operations in `at h1`. Combine the equalities or inequalities in the displayed calculation. Establish `hL : (q.totient : ℝ) / q * Real.log Q ≤ ∑ d ∈ D, (1:ℝ) / d.totient`. Establish `h2` using `sum_inv_le_mul_sum_squarefree_inv_totient Q q hq`. Establish `h3 : (q.totient : ℝ) / q * ((q:ℝ) / q.totient) = 1` using `by field_simp`.

Combine the equalities or inequalities in the displayed calculation. Use `set U : ℕ → ℝ := fun d => ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, (1:ℂ) * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 with hU`. Establish `hmont : ∀ d ∈ D, Z ^ 2 * ((1:ℝ) / d.totient) ≤ U d`. Introduce `d hd`. Rewrite `hd` using `[hD, Finset.mem_filter, Finset.mem_Icc]`.

Establish `hd0 : 0 < d` using `hd.1.1`. Establish `h` using `norm_sum_sq_le_totient_mul_of_avoids_classes S d hd0 hd.2.1 (fun p hp hpd => hcl p hp (le_trans (Nat.le_of_dvd hd0 hpd) hd.1.2) (fun hpq => (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpd hd.2.2) hpq)) (fun _ => 1)`. Establish `hφd : (0:ℝ) < d.totient` using `by exact_mod_cast Nat.totient_pos.2 hd0`. Establish `hsum : ‖∑ n ∈ S, (1:ℂ)‖ ^ 2 = Z ^ 2` using `by simp [hZ]`. Rewrite `h` using `[hsum]`.

Rewrite using `[mul_one_div, div_le_iff₀ hφd]`. Combine the linear relations using `[h, mul_comm (d.totient : ℝ) (U d)]`. Establish `hls : ∑ d ∈ D, U d ≤ ((Q:ℝ) ^ 2 + 2 * Real.pi * N) * Z` using `by set P := D.sigma (fun d => (Finset.range d).filter d.Coprime) with hP set T : Finset ℝ := P.image (fun x => (x.2:ℝ) / x.1) with hT`. Establish `hmemP : ∀ x ∈ P, 0 < x.1 ∧ x.1 ≤ Q ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1`. Introduce `x hx`.

Rewrite `hx` using `[hP, Finset.mem_sigma, hD, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2.symm⟩`. Establish `hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => (x.2:ℝ) / x.1) P`. Introduce `x hx y hy hxy`. Take `⟨h1, -, -, h4⟩` from `hmemP x hx`.

Take `⟨g1, -, -, g4⟩` from `hmemP y hy`. Take `⟨e1, e2⟩` from `_root_.GlobalTheory.MultSieve.reduced_inj h1 g1 h4 g4 hxy`. Conclude with `Sigma.ext e1 (heq_of_eq e2)`. Establish `hsumU : ∑ d ∈ D, U d = ∑ x ∈ T, ‖∑ n ∈ Finset.Ioc M (M + N), (if n ∈ S then (1:ℂ) else 0) * cexp (2 * ↑Real.pi * I * ↑n * ↑x)‖ ^ 2`. Rewrite using `[hT, Finset.sum_image hinj, hP, Finset.sum_sigma]`.

Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [ite_mul, one_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]`. Use `congr 2`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hspaced : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ k : ℤ, 1 / (Q:ℝ) ^ 2 ≤ |x - y - k|`. Introduce `x hx y hy hxy k`.

Take `⟨u, hu, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hy`. Take `⟨-, u2, u3, -⟩` from `hmemP u hu`. Take `⟨-, v2, v3, -⟩` from `hmemP v hv`. Conclude with `_root_.GlobalTheory.MultSieve.farey_spaced Q u.1 v.1 u.2 v.2 u2 v2 u3 v3 hxy k`.

Establish `hQpos : (0:ℝ) < Q` using `by exact_mod_cast hQ`. Establish `h` using `_root_.GlobalTheory.additive_large_sieve M N (fun n => if n ∈ S then (1:ℂ) else 0) T (1 / (Q:ℝ) ^ 2) (by positivity) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by exact_mod_cast hQ)) hspaced`. Rewrite `h` using `[one_div_one_div, ← hsumU]`. Establish `hnorm : ∑ n ∈ Finset.Ioc M (M + N), ‖(if n ∈ S then (1:ℂ) else 0)‖ ^ 2 = Z`. Establish `hpt : ∀ n, ‖(if n ∈ S then (1:ℂ) else 0)‖ ^ 2 = if n ∈ S then (1:ℝ) else 0`.

Apply the tactic sequence `intro n; split_ifs <;> simp`. Repeatedly rewrite using `[hpt]`. Rewrite using `[← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]`. Simplify using `[hZ]`. Rewrite `h` using `[hnorm]`.

Conclude with `h`. Establish `hbig : Z ^ 2 * ∑ d ∈ D, (1:ℝ) / d.totient ≤ ((Q:ℝ) ^ 2 + 2 * Real.pi * N) * Z`. Rewrite using `[Finset.mul_sum]`. Conclude with `le_trans (Finset.sum_le_sum hmont) hls`. Break down `hZ0.eq_or_lt with h0 | hpos` into its components or cases.

Rewrite using `[← h0, zero_mul]`. Conclude with `hRHS`. Combine the equalities or inequalities in the displayed calculation. Use `le_of_mul_le_mul_left ?_ hpos` and prove the remaining obligations. Use polynomial arithmetic with `[hbig]`.
-/
theorem _root_.GlobalTheory.arithmetic_large_sieve_one_class : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q →
    S ⊆ Finset.Ioc M (M + N) →
    (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) →
    (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  intro M N Q q S hQ hq hS hcl
  set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD
  set Z : ℝ := (S.card : ℝ) with hZ
  have hZ0 : 0 ≤ Z := Nat.cast_nonneg _
  have hRHS : 0 ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by positivity

  have hφq : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log Q ≤ ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n := by
    have h1 := log_add_one_le_harmonic Q
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    calc Real.log Q ≤ Real.log (Q + 1) := Real.log_le_log (by exact_mod_cast hQ) (by linarith)
      _ ≤ _ := by simpa [one_div] using h1
  have hL : (q.totient : ℝ) / q * Real.log Q ≤ ∑ d ∈ D, (1:ℝ) / d.totient := by
    have h2 := sum_inv_le_mul_sum_squarefree_inv_totient Q q hq
    have h3 : (q.totient : ℝ) / q * ((q:ℝ) / q.totient) = 1 := by field_simp
    calc (q.totient : ℝ) / q * Real.log Q ≤ (q.totient : ℝ) / q * ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n := by
          gcongr
      _ ≤ (q.totient : ℝ) / q * (((q:ℝ) / q.totient) * ∑ d ∈ D, (1:ℝ) / d.totient) := by gcongr
      _ = _ := by rw [← mul_assoc, h3, one_mul]

  set U : ℕ → ℝ := fun d => ∑ a ∈ (Finset.range d).filter d.Coprime,
    ‖∑ n ∈ S, (1:ℂ) * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 with hU
  have hmont : ∀ d ∈ D, Z ^ 2 * ((1:ℝ) / d.totient) ≤ U d := by
    intro d hd
    rw [hD, Finset.mem_filter, Finset.mem_Icc] at hd
    have hd0 : 0 < d := hd.1.1
    have h := norm_sum_sq_le_totient_mul_of_avoids_classes S d hd0 hd.2.1 (fun p hp hpd => hcl p hp
      (le_trans (Nat.le_of_dvd hd0 hpd) hd.1.2)
      (fun hpq => (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpd hd.2.2) hpq)) (fun _ => 1)
    have hφd : (0:ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 hd0
    have hsum : ‖∑ n ∈ S, (1:ℂ)‖ ^ 2 = Z ^ 2 := by simp [hZ]
    rw [hsum] at h
    rw [mul_one_div, div_le_iff₀ hφd]
    linarith [h, mul_comm (d.totient : ℝ) (U d)]
  have hls : ∑ d ∈ D, U d ≤ ((Q:ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
    set P := D.sigma (fun d => (Finset.range d).filter d.Coprime) with hP
    set T : Finset ℝ := P.image (fun x => (x.2:ℝ) / x.1) with hT
    have hmemP : ∀ x ∈ P, 0 < x.1 ∧ x.1 ≤ Q ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := by
      intro x hx
      rw [hP, Finset.mem_sigma, hD, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
        Finset.mem_range] at hx
      exact ⟨hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2.symm⟩
    have hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => (x.2:ℝ) / x.1) P := by
      intro x hx y hy hxy
      obtain ⟨h1, -, -, h4⟩ := hmemP x hx
      obtain ⟨g1, -, -, g4⟩ := hmemP y hy
      obtain ⟨e1, e2⟩ := _root_.GlobalTheory.MultSieve.reduced_inj h1 g1 h4 g4 hxy
      exact Sigma.ext e1 (heq_of_eq e2)
    have hsumU : ∑ d ∈ D, U d = ∑ x ∈ T, ‖∑ n ∈ Finset.Ioc M (M + N),
        (if n ∈ S then (1:ℂ) else 0) * cexp (2 * ↑Real.pi * I * ↑n * ↑x)‖ ^ 2 := by
      rw [hT, Finset.sum_image hinj, hP, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
      simp only [ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
      congr 2
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      push_cast
      ring
    have hspaced : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ k : ℤ, 1 / (Q:ℝ) ^ 2 ≤ |x - y - k| := by
      intro x hx y hy hxy k
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨-, u2, u3, -⟩ := hmemP u hu
      obtain ⟨-, v2, v3, -⟩ := hmemP v hv
      exact _root_.GlobalTheory.MultSieve.farey_spaced Q u.1 v.1 u.2 v.2 u2 v2 u3 v3 hxy k
    have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
    have h := _root_.GlobalTheory.additive_large_sieve M N (fun n => if n ∈ S then (1:ℂ) else 0) T (1 / (Q:ℝ) ^ 2)
      (by positivity) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by exact_mod_cast hQ)) hspaced
    rw [one_div_one_div, ← hsumU] at h
    have hnorm : ∑ n ∈ Finset.Ioc M (M + N), ‖(if n ∈ S then (1:ℂ) else 0)‖ ^ 2 = Z := by
      have hpt : ∀ n, ‖(if n ∈ S then (1:ℂ) else 0)‖ ^ 2 = if n ∈ S then (1:ℝ) else 0 := by
        intro n; split_ifs <;> simp
      simp_rw [hpt]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
      simp [hZ]
    rw [hnorm] at h
    exact h
  have hbig : Z ^ 2 * ∑ d ∈ D, (1:ℝ) / d.totient ≤ ((Q:ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hmont) hls
  rcases hZ0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact hRHS
  · calc Z * ((q.totient : ℝ) / q * Real.log Q) ≤ Z * ∑ d ∈ D, (1:ℝ) / d.totient :=
          mul_le_mul_of_nonneg_left hL hZ0
      _ ≤ (Q:ℝ) ^ 2 + 2 * Real.pi * N := by
          refine le_of_mul_le_mul_left ?_ hpos
          nlinarith [hbig]

end GlobalTheory
