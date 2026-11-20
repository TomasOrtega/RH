import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SerreTorsion

variable {E : Type} [Ring E]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨y, hy⟩` from `ih`. Use `⟨n.choose 2 • (1 : E) + y * (1 + x), ?_⟩` and prove the remaining obligations.

Establish `hc : (n + 1).choose 2 = n + n.choose 2`. Rewrite using `[Nat.choose_succ_succ' n 1, Nat.choose_one_right]`. Rewrite using `[pow_succ, hy, hc]`. Simplify using `only [add_mul, mul_add, _root_.one_mul, _root_.mul_one, smul_mul_assoc, mul_smul_comm, add_smul, one_smul, pow_succ, pow_zero, _root_.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem one_add_pow_expand (x : E) (n : ℕ) :
    ∃ y : E, (1 + x) ^ n = 1 + n • x + n.choose 2 • x ^ 2 + x ^ 3 * y := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨n.choose 2 • (1 : E) + y * (1 + x), ?_⟩
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, hy, hc]
    simp only [add_mul, mul_add, _root_.one_mul, _root_.mul_one, smul_mul_assoc, mul_smul_comm, add_smul,
      one_smul, pow_succ, pow_zero, _root_.mul_assoc]
    abel

/- English proof (translation)
Take `⟨y, hy⟩` from `one_add_pow_expand (c • ψ) n`. Use `⟨ψ ^ 3 * y, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, smul_pow, smul_pow, smul_mul_assoc]`. Use `module`.
-/
theorem one_add_smul_pow_expand (c : ℕ) (ψ : E) (n : ℕ) :
    ∃ z : E, (1 + c • ψ) ^ n = 1 + c • (n • ψ + (n.choose 2 * c) • ψ ^ 2 + (c ^ 2) • z) := by
  obtain ⟨y, hy⟩ := one_add_pow_expand (c • ψ) n
  refine ⟨ψ ^ 3 * y, ?_⟩
  rw [hy, smul_pow, smul_pow, smul_mul_assoc]
  module

/- English proof (translation)
Take `⟨z, hz⟩` from `one_add_smul_pow_expand c ψ l`. Rewrite `hz` using `[h]`. Establish `h0` using `htf c _ hc0 (left_eq_add.mp hz)`. Take `⟨d, rfl⟩` from `hqc`. Distinguish the cases in `hlq : l = q`.

Substitute `hlq` using the available equality. Establish `hdiv : l ∣ l.choose 2 * d`. Distinguish the cases in `hl2 : l = 2`. Substitute `hl2` using the available equality. Use `h2 rfl` as an intermediate fact.

Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Use `hl.two_le` as an intermediate fact. Conclude with `Dvd.dvd.mul_right (hl.dvd_choose_self (by norm_num) (by omega)) _`. Take `⟨e, he⟩` from `hdiv`.

Establish `h1 : l • (ψ + l • (e • ψ ^ 2 + (d ^ 2) • z)) = 0`. Rewrite using `[← h0, mul_left_comm, he]`. Use `module`. Establish `h3` using `htf l _ hl.ne_zero h1`. Conclude with `⟨-(e • ψ ^ 2 + (d ^ 2) • z), by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h3⟩`.

Establish `hcop : IsCoprime (l : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hq).mpr hlq)`. Take `⟨u, v, huv⟩` from `hcop`. Use `⟨v • ψ - u • ((l.choose 2 * d) • ψ ^ 2 + (q * d ^ 2) • z), ?_⟩` and prove the remaining obligations. Establish `h1 : ψ = (u * l + v * q) • ψ` using `by rw [huv, one_smul]`. Establish `h4 : ψ = (u * l + v * q) • ψ - u • (l • ψ + (l.choose 2 * (q * d)) • ψ ^ 2 + ((q * d) ^ 2) • z)`.

Rewrite using `[h0, smul_zero, sub_zero]`. Conclude with `h1`. Use `h4.trans ?_` and prove the remaining obligations. Use `module`.
-/
theorem step (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ} (hq : q.Prime)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ∃ y : E, ψ = q • y := by
  obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
  rw [h] at hz
  have h0 := htf c _ hc0 (left_eq_add.mp hz)
  obtain ⟨d, rfl⟩ := hqc
  by_cases hlq : l = q
  · subst hlq
    have hdiv : l ∣ l.choose 2 * d := by
      by_cases hl2 : l = 2
      · subst hl2
        have := h2 rfl
        apply Dvd.dvd.mul_left
        omega
      · have := hl.two_le
        exact Dvd.dvd.mul_right (hl.dvd_choose_self (by norm_num) (by omega)) _
    obtain ⟨e, he⟩ := hdiv
    have h1 : l • (ψ + l • (e • ψ ^ 2 + (d ^ 2) • z)) = 0 := by
      rw [← h0, mul_left_comm, he]
      module
    have h3 := htf l _ hl.ne_zero h1
    exact ⟨-(e • ψ ^ 2 + (d ^ 2) • z), by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h3⟩
  · have hcop : IsCoprime (l : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hq).mpr hlq)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨v • ψ - u • ((l.choose 2 * d) • ψ ^ 2 + (q * d ^ 2) • z), ?_⟩
    have h1 : ψ = (u * l + v * q) • ψ := by rw [huv, one_smul]
    have h4 : ψ = (u * l + v * q) • ψ
        - u • (l • ψ + (l.choose 2 * (q * d)) • ψ ^ 2 + ((q * d) ^ 2) • z) := by
      rw [h0, smul_zero, sub_zero]; exact h1
    refine h4.trans ?_
    module

/- English proof (translation)
Apply `hsep` to reduce the goal to its premises. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨ψ, by simp⟩`. Consider the case `succ k ih`.

Take `⟨y, hy⟩` from `ih`. Establish `h' : (1 + (c * q ^ k) • y) ^ l = 1` using `by rw [mul_smul, ← hy, h]`. Take `⟨w, hw⟩` from `step htf hq hl (mul_ne_zero hc0 (pow_ne_zero k hq.ne_zero)) (hqc.mul_right _) (fun hq2 => (h2 hq2).mul_right _) y h'`. Conclude with `⟨w, by rw [hy, hw, pow_succ, mul_smul]⟩`.
-/
theorem eq_zero_of_prime (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ψ = 0 := by
  apply hsep
  intro k
  induction k with
  | zero => exact ⟨ψ, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    have h' : (1 + (c * q ^ k) • y) ^ l = 1 := by rw [mul_smul, ← hy, h]
    obtain ⟨w, hw⟩ := step htf hq hl (mul_ne_zero hc0 (pow_ne_zero k hq.ne_zero))
      (hqc.mul_right _) (fun hq2 => (h2 hq2).mul_right _) y h'
    exact ⟨w, by rw [hy, hw, pow_succ, mul_smul]⟩

/- English proof (translation)
Proceed by induction on `m using induction_on_primes with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one => intro _ ψ h`. Simplify `h` using `only [pow_one]`.

Consider the case `prime_mul l a hl ih`. Introduce `hm ψ h`. Establish `ha : a ≠ 0` using `right_ne_zero_of_mul hm`. Take `⟨z, hz⟩` from `one_add_smul_pow_expand c ψ l`. Rewrite `h` using `[pow_mul, hz]`.

Establish `h1` using `ih ha _ h`. Rewrite `h1` using `[← hz]`. Rewrite using `[eq_zero_of_prime htf hq hsep hl hc0 hqc h2 ψ h1, smul_zero, add_zero]`.
-/
theorem eq_one_of_pow (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (m : ℕ) :
    m ≠ 0 → ∀ ψ : E, (1 + c • ψ) ^ m = 1 → 1 + c • ψ = 1 := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ ψ h; simpa only [pow_one] using h
  | prime_mul l a hl ih =>
    intro hm ψ h
    have ha : a ≠ 0 := right_ne_zero_of_mul hm
    obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
    rw [pow_mul, hz] at h
    have h1 := ih ha _ h
    rw [← hz] at h1
    rw [eq_zero_of_prime htf hq hsep hl hc0 hqc h2 ψ h1, smul_zero, add_zero]

end SerreTorsion

/- English proof (translation)
Introduce `E _ M hM htf hsep σ φ m hm hσ h`. Establish `hq : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q = 2 → 4 ∣ M)`. Break down `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < M) with h4 | ⟨p, hp, hpM, hodd⟩` into its components or cases. Conclude with `⟨2, Nat.prime_two, Dvd.dvd.trans (by norm_num) h4, fun _ => h4⟩`. Use `⟨p, hp, hpM, fun h2 => ?_⟩` and prove the remaining obligations.

Substitute `h2` using the available equality. Conclude with `absurd hodd (by decide)`. Take `⟨q, hq, hqM, h2⟩` from `hq`. Rewrite `hσ` using `[← nsmul_eq_mul]`. Substitute `hσ` using the available equality.

Use `SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hq (fun x hx => hsep q x hq.two_le fun k => ?_) (by omega) hqM h2 m hm φ h` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx k`. Conclude with `⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩`.
-/
theorem eq_one_of_pow_eq_one_of_congr_one :
    ∀ (E : Type) [Ring E] (M : ℕ), 3 ≤ M → (∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0) → (∀ (q : ℕ) (x : E), 2 ≤ q → (∀ k : ℕ, ∃ y : E, x = (q : E) ^ k * y) → x = 0) → ∀ (σ φ : E) (m : ℕ), m ≠ 0 → σ = 1 + (M : E) * φ → σ ^ m = 1 → σ = 1 := by
  intro E _ M hM htf hsep σ φ m hm hσ h
  have hq : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q = 2 → 4 ∣ M) := by
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < M) with
      h4 | ⟨p, hp, hpM, hodd⟩
    · exact ⟨2, Nat.prime_two, Dvd.dvd.trans (by norm_num) h4, fun _ => h4⟩
    · refine ⟨p, hp, hpM, fun h2 => ?_⟩
      subst h2
      exact absurd hodd (by decide)
  obtain ⟨q, hq, hqM, h2⟩ := hq
  rw [← nsmul_eq_mul] at hσ
  subst hσ
  refine SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hq
    (fun x hx => hsep q x hq.two_le fun k => ?_) (by omega) hqM h2 m hm φ h
  obtain ⟨y, hy⟩ := hx k
  exact ⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩

end GlobalTheory
