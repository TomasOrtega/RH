import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Establish `n_pos : 0 < n` using `(Nat.zero_le _).trans_lt n_large`. Establish `n2_pos : 1 ≤ 2 * n` using `mul_pos (zero_lt_two' ℕ) n_pos`. Set `S` to `{p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}`. Set `T` to `(Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)`. Set `f : ℕ → ℕ` to `fun x => x ^ n.centralBinom.factorization x`.

Establish `hf : ∀ p, f p ≤ 2 * n` using `fun p => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)`. Establish `hdisj : Disjoint S T`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hy`. Establish `h1` using `Finset.mem_range.1 (Finset.mem_filter.1 hx).1`.

Establish `h2` using `(Finset.mem_filter.1 hy).2.2`. Use linear arithmetic over natural numbers and integers. Establish `key : n.centralBinom = (∏ x ∈ S, f x) * ∏ x ∈ T, f x`. Rewrite using `[← Finset.prod_union hdisj]`. Use `(Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm` and prove the remaining obligations.

Apply `Finset.prod_subset` to reduce the goal to its premises. Introduce `x hx`. Break down `Finset.mem_union.1 hx with h | h` into its components or cases. Establish `h1` using `Finset.mem_range.1 (Finset.mem_filter.1 h).1`. Rewrite using `[Finset.mem_range]`.

Use linear arithmetic over natural numbers and integers. Conclude with `(Finset.mem_filter.1 h).1`. Introduce `x hx h2x`. Distinguish the cases in `hp : x.Prime`. Establish `h1 : ¬ x < 2 * n / 3 + 1` using `fun h => h2x (Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hp⟩)))`.

Establish `h2 : ¬ n < x` using `fun h => h2x (Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hx, hp, h⟩)))`. Establish `h3 : 2 * n < 3 * x` using `by omega`. Simplify using `only [f]`. Rewrite using `[Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large (not_lt.1 h2) h3, Nat.pow_zero]`. Simplify using `only [f]`.

Rewrite using `[Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, Nat.pow_zero]`. Rewrite using `[key]`. Apply `mul_le_mul'` to reduce the goal to its premises. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]`. Apply `mul_le_mul'` to reduce the goal to its premises.

Use `(Finset.prod_le_prod' fun p _ => hf p).trans ?_` and prove the remaining obligations. Establish `: (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n)`. Rewrite using `[Nat.card_Icc, Nat.add_sub_cancel]`. Rewrite using `[Finset.prod_const]`. Use `pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hx`. Conclude with `Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩`. Use `le_trans ?_ (primorial_le_four_pow (2 * n / 3))` and prove the remaining obligations. Use `(Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hp`.

Use `(pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le` and prove the remaining obligations. Conclude with `Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)`. Use `Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_` and prove the remaining obligations. Conclude with `fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le`. Use `(Finset.prod_le_prod' fun p _ => hf p).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_const]`.
-/
theorem centralBinom_le_pow_card_primes_between (n : ℕ) (n_large : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h1 := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have h2 := (Finset.mem_filter.1 hy).2.2
    omega
  have key : n.centralBinom = (∏ x ∈ S, f x) * ∏ x ∈ T, f x := by
    rw [← Finset.prod_union hdisj]
    refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
    apply Finset.prod_subset
    · intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · have h1 := Finset.mem_range.1 (Finset.mem_filter.1 h).1
        rw [Finset.mem_range]; omega
      · exact (Finset.mem_filter.1 h).1
    intro x hx h2x
    by_cases hp : x.Prime
    · have h1 : ¬ x < 2 * n / 3 + 1 := fun h => h2x (Finset.mem_union.2 (Or.inl
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hp⟩)))
      have h2 : ¬ n < x := fun h => h2x (Finset.mem_union.2 (Or.inr
        (Finset.mem_filter.2 ⟨hx, hp, h⟩)))
      have h3 : 2 * n < 3 * x := by omega
      simp only [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large (not_lt.1 h2) h3,
        Nat.pow_zero]
    · simp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, Nat.pow_zero]
  rw [key]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]

open Polynomial Classical in
/- English proof (translation)
Use `set s := Nat.sqrt (2 * m) with hs`. Establish `hone : ∀ (P : Prop) [Decidable P] (p : ℕ), (P → 1 ≤ p) → 1 ≤ (if P then p else 1)`. Introduce `P _ p h`. Use `split_ifs with hP`. Use `exacts [h hP, le_rfl]`.

Establish `key : ∀ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p ≤ (if p ≤ s then 2 * m else 1) * (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) * (if p.Prime ∧ m < p then p else 1)`. Introduce `p _`. Establish `hB : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1)` using `hone _ _ fun h => h.1.one_lt.le`. Establish `hC : 1 ≤ (if p.Prime ∧ m < p then p else 1)` using `hone _ _ fun h => h.1.one_lt.le`. Establish `hBC : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) * (if p.Prime ∧ m < p then p else 1)` using `le_trans (by norm_num) (Nat.mul_le_mul hB hC)`.

Distinguish the cases in `h1 : p ≤ s`. Rewrite using `[if_pos h1]`. Establish `h2 : p ^ m.centralBinom.factorization p ≤ 2 * m`. Rewrite using `[Nat.centralBinom_eq_two_mul_choose]`. Conclude with `Nat.pow_factorization_choose_le (by omega)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[if_neg h1, one_mul]`. Establish `hsq : 2 * m < p ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `hv : m.centralBinom.factorization p ≤ 1`.

Rewrite using `[Nat.centralBinom_eq_two_mul_choose]`. Conclude with `Nat.factorization_choose_le_one hsq`. Distinguish the cases in `hp : p.Prime`. Distinguish the cases in `h3 : p ≤ 2 * m / 3`. Establish `h4 : ¬ m < p` using `by omega`.

Rewrite using `[if_pos ⟨hp, h3⟩, if_neg (fun h => h4 h.2), mul_one]`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `h5 : m < p`. Rewrite using `[if_neg (fun h => h3 h.2), if_pos ⟨hp, h5⟩, one_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h0 : m.centralBinom.factorization p = 0` using `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm (by omega) (by omega)`. Rewrite using `[h0, pow_zero]`. Conclude with `hBC`. Rewrite using `[Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]`. Conclude with `hBC`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib]`. Use `_ ≤ _ := by gcongr ?_ * ?_ * ?_`. Rewrite using `[← Finset.prod_filter, Finset.prod_const]`. Apply `Nat.pow_le_pow_right (by omega)` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hx ⊢`. Use linear arithmetic over natural numbers and integers.

Use `_ = s + 1 := Finset.card_range _`. Rewrite using `[← Finset.prod_filter]`. Combine the equalities or inequalities in the displayed calculation. Unfold `primorial`. Use `congr 1`.

Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h2, h3⟩`. Conclude with `⟨by omega, h2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by omega, h2, by omega⟩`. Use `_ ≤ 4 ^ (2 * m / 3) := primorial_le_4_pow _`. Rewrite using `[← Finset.prod_filter]`.
-/
private lemma centralBinom_le_pow_mul_four_pow_mul_prod_large_primes (m : ℕ) (hm : 2 < m) :
    m.centralBinom ≤ (2 * m) ^ (Nat.sqrt (2 * m) + 1) * 4 ^ (2 * m / 3) *
      ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p := by
  set s := Nat.sqrt (2 * m) with hs
  have hone : ∀ (P : Prop) [Decidable P] (p : ℕ), (P → 1 ≤ p) → 1 ≤ (if P then p else 1) := by
    intro P _ p h
    split_ifs with hP
    exacts [h hP, le_rfl]
  have key : ∀ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p ≤
      (if p ≤ s then 2 * m else 1) * (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := by
    intro p _
    have hB : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) :=
      hone _ _ fun h => h.1.one_lt.le
    have hC : 1 ≤ (if p.Prime ∧ m < p then p else 1) := hone _ _ fun h => h.1.one_lt.le
    have hBC : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := le_trans (by norm_num) (Nat.mul_le_mul hB hC)
    by_cases h1 : p ≤ s
    · rw [if_pos h1]
      have h2 : p ^ m.centralBinom.factorization p ≤ 2 * m := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le (by omega)
      calc p ^ m.centralBinom.factorization p ≤ 2 * m * 1 * 1 := by simpa using h2
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hB) hC
    · rw [if_neg h1, one_mul]
      have hsq : 2 * m < p ^ 2 :=
        calc 2 * m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' (2 * m)
          _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hv : m.centralBinom.factorization p ≤ 1 := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.factorization_choose_le_one hsq
      by_cases hp : p.Prime
      · by_cases h3 : p ≤ 2 * m / 3
        · have h4 : ¬ m < p := by omega
          rw [if_pos ⟨hp, h3⟩, if_neg (fun h => h4 h.2), mul_one]
          calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
            _ = p := pow_one p
        · by_cases h5 : m < p
          · rw [if_neg (fun h => h3 h.2), if_pos ⟨hp, h5⟩, one_mul]
            calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
              _ = p := pow_one p
          · have h0 : m.centralBinom.factorization p = 0 :=
              Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm (by omega) (by omega)
            rw [h0, pow_zero]
            exact hBC
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
        exact hBC
  calc m.centralBinom
      = ∏ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p :=
        (Nat.prod_pow_factorization_centralBinom m).symm
    _ ≤ ∏ p ∈ Finset.range (2 * m + 1), ((if p ≤ s then 2 * m else 1) *
          (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) * (if p.Prime ∧ m < p then p else 1)) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) key
    _ = (∏ p ∈ Finset.range (2 * m + 1), (if p ≤ s then 2 * m else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ m < p then p else 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
        gcongr ?_ * ?_ * ?_
        · rw [← Finset.prod_filter, Finset.prod_const]
          apply Nat.pow_le_pow_right (by omega)
          calc ((Finset.range (2 * m + 1)).filter (fun p => p ≤ s)).card
              ≤ (Finset.range (s + 1)).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
                omega
            _ = s + 1 := Finset.card_range _
        · rw [← Finset.prod_filter]
          calc ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ p ≤ 2 * m / 3), p
              = primorial (2 * m / 3) := by
                unfold primorial
                congr 1
                ext p
                simp only [Finset.mem_filter, Finset.mem_range]
                constructor
                · rintro ⟨_, h2, h3⟩
                  exact ⟨by omega, h2⟩
                · rintro ⟨h1, h2⟩
                  exact ⟨by omega, h2, by omega⟩
            _ ≤ 4 ^ (2 * m / 3) := primorial_le_4_pow _
        · rw [← Finset.prod_filter]

open Polynomial Classical in

/- English proof (translation)
Introduce `N hN`. Use `set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hS`. Use `set m := N / 2 with hm`. Use `set s := Nat.sqrt (2 * m) with hs`. Use `set k := S.card with hk`.

Use `set q := 2 * m / 3 with hq`. Establish `hm3 : 2 < m` using `by omega`. Establish `hT : ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p ≤ N ^ 3 * N ^ k`. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)) (· ∈ S), mul_comm]`. Apply `Nat.mul_le_mul` to reduce the goal to its premises.

Establish `hsub : ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter (fun x => x ∉ S) ⊆ Finset.Icc (N - 2) N`. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hx`. Take `⟨⟨h1, h2, h3⟩, h4⟩` from `hx`. Establish `h5 : ¬ (x + 3 ≤ N)` using `fun h5 => h4 (by`.

Rewrite using `[hS]`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨by omega, h2, by omega, h5⟩)`. Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation. Apply `Nat.pow_le_pow_right (by omega)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod_of_subset_of_one_le'` to reduce the goal to its premises.

Introduce `x hx`. Conclude with `(Finset.mem_filter.mp hx).2`. Introduce `x hx _`. Rewrite `hx` using `[hS]`. Conclude with `(Finset.mem_filter.mp hx).2.1.one_lt.le`.

Use `_ ≤ N ^ k := Finset.prod_le_pow_card _ _ _ (fun x hx => by`. Rewrite `hx` using `[hS]`. Use `(Finset.mem_filter.mp hx).1` as an intermediate fact. Rewrite `this` using `[Finset.mem_range]`. Use the proof step `omega)`.

Establish `hnat : 4 ^ m < N ^ (s + 5 + k) * 4 ^ q`. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers. Use `_ = N ^ (s + 5 + k) * 4 ^ q := by ring`. Establish `hN0 : (0 : ℝ) < N` using `by exact_mod_cast (by omega : 0 < N)`.

Establish `hreal : (m : ℝ) * Real.log 4 < (s + 5 + k) * Real.log N + q * Real.log 4`. Establish `h' : (4 : ℝ) ^ m < (N : ℝ) ^ (s + 5 + k) * (4 : ℝ) ^ q` using `by exact_mod_cast hnat`. Establish `h2` using `Real.log_lt_log (by positivity) h'`. Rewrite `h2` using `[Real.log_mul (pow_pos hN0 _).ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]`. Move the coercions through the operations in `at h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq3 : (3 : ℝ) * q ≤ 2 * m` using `by exact_mod_cast (by omega : 3 * q ≤ 2 * m)`. Establish `hmN : (N : ℝ) ≤ 2 * m + 1` using `by exact_mod_cast (by omega : N ≤ 2 * m + 1)`. Establish `hs2 : (s : ℝ) ^ 2 ≤ N`. Establish `: s ^ 2 ≤ N` using `le_trans (Nat.sqrt_le' (2 * m)) (by omega)`.

Conclude with `this` after adjusting the coercions. Use `set t := Real.sqrt N with ht`. Establish `ht0 : 0 ≤ t` using `Real.sqrt_nonneg _`. Establish `ht2 : t ^ 2 = N` using `Real.sq_sqrt hN0.le`. Establish `hNbig : (100000 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hst : (s : ℝ) ≤ t` using `by nlinarith [Nat.cast_nonneg (α := ℝ) s]`. Establish `htlow : (316 : ℝ) ≤ t` using `by nlinarith`. Establish `hL : Real.log N ≤ 7.72 + t / 50`. Establish `h1` using `Real.log_le_sub_one_of_pos (x := t / 100) (by positivity)`. Rewrite `h1` using `[Real.log_div (by positivity) (by norm_num)]`.

Establish `h2 : Real.log t = Real.log N / 2` using `by rw [ht, Real.log_sqrt hN0.le]`. Establish `h3 : Real.log 100 < 4.86`. Establish `: Real.log 100 < Real.log (2 ^ 7)` using `Real.log_lt_log (by norm_num) (by norm_num)`. Rewrite `this` using `[Real.log_pow]`. Move the coercions through the operations in `at this`.

Combine the linear relations using `[Real.log_two_lt_d9]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL4 : 1.386 < Real.log 4`. Establish `: Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`.

Evaluate the numerical expressions. Combine the linear relations using `[Real.log_two_gt_d9]`. Establish `hLpos : 0 < Real.log N` using `Real.log_pos (by linarith)`. Establish `hsum : (k : ℝ) * (1 / N) ≤ ∑ p ∈ S, (1 : ℝ) / p`. Rewrite using `[hk, ← nsmul_eq_mul, ← Finset.sum_const]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[hS]`. Take `⟨h1, h2, _⟩` from `Finset.mem_filter.mp hp`. Rewrite `h1` using `[Finset.mem_range]`.

Apply `one_div_le_one_div_of_le (by exact_mod_cast h2.pos)` to reduce the goal to its premises. Conclude with `(by omega : p ≤ N)` after adjusting the coercions. Establish `hA : ((m : ℝ) - q) * 1.386 ≤ (m : ℝ) * Real.log 4 - q * Real.log 4`. Use the polynomial consequences of the given equalities and inequalities. Establish `hB : ((s : ℝ) + 5) * Real.log N ≤ (t + 5) * (7.72 + t / 50)` using `mul_le_mul (by linarith) hL hLpos.le (by positivity)`.

Establish `hkey : (N : ℝ) ≤ k * (10 * Real.log N)`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr htlow) ht0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one_div, div_le_div_iff₀ (by positivity) hN0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ ≤ _ := hsum`.
-/
theorem _root_.GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between :
    ∀ N : ℕ, 100000 ≤ N → 1 / (10 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hS
  set m := N / 2 with hm
  set s := Nat.sqrt (2 * m) with hs
  set k := S.card with hk
  set q := 2 * m / 3 with hq
  have hm3 : 2 < m := by omega
  have hT : ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p ≤
      N ^ 3 * N ^ k := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)) (· ∈ S), mul_comm]
    apply Nat.mul_le_mul
    · have hsub : ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
          (fun x => x ∉ S) ⊆ Finset.Icc (N - 2) N := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
        have h5 : ¬ (x + 3 ≤ N) := fun h5 => h4 (by
          rw [hS]
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, h2, by omega, h5⟩)
        rw [Finset.mem_Icc]
        omega
      calc _ ≤ N ^ (((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
            (fun x => x ∉ S)).card :=
            Finset.prod_le_pow_card _ _ _ (fun x hx => (Finset.mem_Icc.mp (hsub hx)).2)
        _ ≤ N ^ 3 := by
            apply Nat.pow_le_pow_right (by omega)
            calc _ ≤ (Finset.Icc (N - 2) N).card := Finset.card_le_card hsub
              _ = 3 := by rw [Nat.card_Icc]; omega
    · calc _ ≤ ∏ x ∈ S, x := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · intro x hx
              exact (Finset.mem_filter.mp hx).2
            · intro x hx _
              rw [hS] at hx
              exact (Finset.mem_filter.mp hx).2.1.one_lt.le
        _ ≤ N ^ k := Finset.prod_le_pow_card _ _ _ (fun x hx => by
            rw [hS] at hx
            have := (Finset.mem_filter.mp hx).1
            rw [Finset.mem_range] at this
            omega)
  have hnat : 4 ^ m < N ^ (s + 5 + k) * 4 ^ q := by
    calc 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m (by omega)
      _ ≤ N * ((2 * m) ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) :=
          Nat.mul_le_mul (by omega)
            (le_trans (centralBinom_le_pow_mul_four_pow_mul_prod_large_primes m hm3)
              (Nat.mul_le_mul_left _ hT))
      _ ≤ N * (N ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) := by
          gcongr
          omega
      _ = N ^ (s + 5 + k) * 4 ^ q := by ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hreal : (m : ℝ) * Real.log 4 < (s + 5 + k) * Real.log N + q * Real.log 4 := by
    have h' : (4 : ℝ) ^ m < (N : ℝ) ^ (s + 5 + k) * (4 : ℝ) ^ q := by exact_mod_cast hnat
    have h2 := Real.log_lt_log (by positivity) h'
    rw [Real.log_mul (pow_pos hN0 _).ne' (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow] at h2
    push_cast at h2
    linarith
  have hq3 : (3 : ℝ) * q ≤ 2 * m := by exact_mod_cast (by omega : 3 * q ≤ 2 * m)
  have hmN : (N : ℝ) ≤ 2 * m + 1 := by exact_mod_cast (by omega : N ≤ 2 * m + 1)
  have hs2 : (s : ℝ) ^ 2 ≤ N := by
    have : s ^ 2 ≤ N := le_trans (Nat.sqrt_le' (2 * m)) (by omega)
    exact_mod_cast this
  set t := Real.sqrt N with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = N := Real.sq_sqrt hN0.le
  have hNbig : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hst : (s : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have htlow : (316 : ℝ) ≤ t := by nlinarith
  have hL : Real.log N ≤ 7.72 + t / 50 := by
    have h1 := Real.log_le_sub_one_of_pos (x := t / 100) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    have h2 : Real.log t = Real.log N / 2 := by rw [ht, Real.log_sqrt hN0.le]
    have h3 : Real.log 100 < 4.86 := by
      have : Real.log 100 < Real.log (2 ^ 7) := Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at this
      push_cast at this
      linarith [Real.log_two_lt_d9]
    linarith
  have hL4 : 1.386 < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hsum : (k : ℝ) * (1 / N) ≤ ∑ p ∈ S, (1 : ℝ) / p := by
    rw [hk, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [hS] at hp
    obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_range] at h1
    apply one_div_le_one_div_of_le (by exact_mod_cast h2.pos)
    exact_mod_cast (by omega : p ≤ N)
  have hA : ((m : ℝ) - q) * 1.386 ≤ (m : ℝ) * Real.log 4 - q * Real.log 4 := by
    nlinarith
  have hB : ((s : ℝ) + 5) * Real.log N ≤ (t + 5) * (7.72 + t / 50) :=
    mul_le_mul (by linarith) hL hLpos.le (by positivity)
  have hkey : (N : ℝ) ≤ k * (10 * Real.log N) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htlow) ht0]
  calc 1 / (10 * Real.log N) ≤ k * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hN0]
        linarith
    _ ≤ _ := hsum

end GlobalTheory.BadShare
