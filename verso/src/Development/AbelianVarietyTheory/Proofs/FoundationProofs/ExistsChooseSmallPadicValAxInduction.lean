import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `haveI := Fact.mk hp`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `N h1 h2 hdvd`.

Simplify using `only [pow_zero, zero_add, pow_one, Nat.choose_one_right] at h1 h2 hdvd`. Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `N h1 h2 hdvd`.

Establish `hmod` using `Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := p ^ (k + 1)) (p := p)`. Rewrite `hmod` using `[pow_succ, Nat.mul_mod_left, Nat.choose_zero_right, one_mul, Nat.mul_div_cancel _ hp.pos, ← pow_succ]`. Use `ih (N / p) ?_ ?_ ((hmod.dvd_iff (dvd_refl p)).1 hdvd)` and prove the remaining obligations. Conclude with `(Nat.le_div_iff_mul_le hp.pos).2 (by rw [← pow_succ]; exact h1)`. Conclude with `(Nat.div_lt_iff_lt_mul hp.pos).2 (by rw [← pow_succ]; exact h2)`.
-/
private lemma not_dvd_choose_prime_pow_of_between {p : ℕ} (hp : p.Prime) :
    ∀ (k N : ℕ), p ^ k ≤ N → N < p ^ (k + 1) → ¬ p ∣ N.choose (p ^ k) := by
  haveI := Fact.mk hp
  intro k
  induction k with
  | zero =>
    intro N h1 h2 hdvd
    simp only [pow_zero, zero_add, pow_one, Nat.choose_one_right] at h1 h2 hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  | succ k ih =>
    intro N h1 h2 hdvd
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := p ^ (k + 1))
      (p := p)
    rw [pow_succ, Nat.mul_mod_left, Nat.choose_zero_right, one_mul,
      Nat.mul_div_cancel _ hp.pos, ← pow_succ] at hmod
    refine ih (N / p) ?_ ?_ ((hmod.dvd_iff (dvd_refl p)).1 hdvd)
    · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [← pow_succ]; exact h1)
    · exact (Nat.div_lt_iff_lt_mul hp.pos).2 (by rw [← pow_succ]; exact h2)

/- English proof (translation)
Introduce `p hp N hN`. Establish `hp1 : 1 < p` using `hp.one_lt`. Take `⟨k, hk⟩ : ∃ k, Nat.log p N = k` from `⟨_, rfl⟩`. Establish `hkle : p ^ k ≤ N` using `hk ▸ Nat.pow_log_le_self p (by omega)`. Establish `hlt : N < p ^ (k + 1)` using `hk ▸ Nat.lt_pow_succ_log_self hp1 N`.

Establish `hpk : 0 < p ^ k` using `pow_pos hp.pos k`. Break down `hkle.lt_or_eq with hlt' | heq` into its components or cases. Use `⟨N - p ^ k, 0, by omega, by omega, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.choose_symm_of_eq_add (b := p ^ k) (by omega), zero_add, pow_one]`. Conclude with `not_dvd_choose_prime_pow_of_between hp k N hkle hlt`.

Establish `hm : N - (N - p ^ k) = p ^ k` using `by omega`. Rewrite using `[hm, Nat.log_pow hp1, hk]`. Simplify using the standard rewrite rules. Substitute `heq` using the available equality. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hN`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Establish `hpk' : 0 < p ^ k'` using `pow_pos hp.pos k'`. Establish `hsucc : p ^ (k' + 1) = p ^ k' * p` using `pow_succ p k'`.

Establish `h2 : 2 * p ^ k' ≤ p ^ (k' + 1)`. Rewrite using `[hsucc, mul_comm]`. Conclude with `Nat.mul_le_mul le_rfl hp.two_le`. Use `⟨p ^ k', 1, hpk', by omega, ?_, ?_⟩` and prove the remaining obligations. Establish `hmult` using `hp.emultiplicity_choose_prime_pow (n := k' + 1) (k := p ^ k') (by omega) (pow_ne_zero _ hp.ne_zero)`.

Rewrite `hmult` using `[multiplicity_pow_self_of_prime hp.prime k']`. Rewrite using `[pow_dvd_iff_le_emultiplicity, hmult]`. Evaluate the numerical expressions. Establish `hlogm : Nat.log p (p ^ (k' + 1) - p ^ k') = k'` using `Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)`. Establish `hcast : ((p ^ (k' + 1) - p ^ k' : ℕ) : ℚ) = (p : ℚ) ^ k' * ((p : ℚ) - 1)`.

Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : (p : ℚ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hp1' : (p : ℚ) - 1 ≠ 0`.

Establish `: (1 : ℚ) < p` using `by exact_mod_cast hp1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hlogm, Nat.log_pow hp1, hcast]`. Apply `le_of_eq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.exists_choose_small_valuation_ax : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N →
    ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  intro p hp N hN
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨k, hk⟩ : ∃ k, Nat.log p N = k := ⟨_, rfl⟩
  have hkle : p ^ k ≤ N := hk ▸ Nat.pow_log_le_self p (by omega)
  have hlt : N < p ^ (k + 1) := hk ▸ Nat.lt_pow_succ_log_self hp1 N
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  rcases hkle.lt_or_eq with hlt' | heq
  · refine ⟨N - p ^ k, 0, by omega, by omega, ?_, ?_⟩
    · rw [Nat.choose_symm_of_eq_add (b := p ^ k) (by omega), zero_add, pow_one]
      exact not_dvd_choose_prime_pow_of_between hp k N hkle hlt
    · have hm : N - (N - p ^ k) = p ^ k := by omega
      rw [hm, Nat.log_pow hp1, hk]
      simp
  · subst heq
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hN
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpk' : 0 < p ^ k' := pow_pos hp.pos k'
    have hsucc : p ^ (k' + 1) = p ^ k' * p := pow_succ p k'
    have h2 : 2 * p ^ k' ≤ p ^ (k' + 1) := by
      rw [hsucc, mul_comm]; exact Nat.mul_le_mul le_rfl hp.two_le
    refine ⟨p ^ k', 1, hpk', by omega, ?_, ?_⟩
    · have hmult := hp.emultiplicity_choose_prime_pow (n := k' + 1) (k := p ^ k')
        (by omega) (pow_ne_zero _ hp.ne_zero)
      rw [multiplicity_pow_self_of_prime hp.prime k'] at hmult
      rw [pow_dvd_iff_le_emultiplicity, hmult]
      norm_num
    · have hlogm : Nat.log p (p ^ (k' + 1) - p ^ k') = k' :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
      have hcast : ((p ^ (k' + 1) - p ^ k' : ℕ) : ℚ) = (p : ℚ) ^ k' * ((p : ℚ) - 1) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hp1' : (p : ℚ) - 1 ≠ 0 := by
        have : (1 : ℚ) < p := by exact_mod_cast hp1
        linarith
      rw [hlogm, Nat.log_pow hp1, hcast]
      apply le_of_eq
      field_simp
      ring

end GlobalTheory
