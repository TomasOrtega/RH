import Mathlib

open Polynomial

namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg

/- English proof (translation)
Establish `h1 : aeval (t : ℤ_[p]) (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p])) = ((a * t ^ 2 + b : ℤ) : ℤ_[p])`. Simplify using the standard rewrite rules. Establish `h2 : aeval (t : ℤ_[p]) (derivative (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))) = ((2 * a * t : ℤ) : ℤ_[p])`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Take `⟨z, hz, -⟩` from `hensels_lemma (F := C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p])) (a := (t : ℤ_[p])) (by rw [h1, h2]; exact h)`. Conclude with `⟨z, by simpa using hz⟩`.
-/
theorem hensel_quad (p : ℕ) [Fact p.Prime] (a b t : ℤ)
    (h : ‖((a * t ^ 2 + b : ℤ) : ℤ_[p])‖ < ‖((2 * a * t : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ z : ℤ_[p], (a : ℤ_[p]) * z ^ 2 + (b : ℤ_[p]) = 0 := by
  have h1 : aeval (t : ℤ_[p]) (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p])) =
      ((a * t ^ 2 + b : ℤ) : ℤ_[p]) := by
    simp
  have h2 : aeval (t : ℤ_[p]) (derivative (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))) =
      ((2 * a * t : ℤ) : ℤ_[p]) := by
    simp
    ring
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))
    (a := (t : ℤ_[p])) (by rw [h1, h2]; exact h)
  exact ⟨z, by simpa using hz⟩

/- English proof (translation)
Use `le_antisymm (PadicInt.norm_le_one _) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Conclude with `h ((PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := k)).1 (not_le.1 hlt))`.
-/
theorem norm_unit (p : ℕ) [Fact p.Prime] (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : ‖(k : ℤ_[p])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  exact h ((PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := k)).1 (not_le.1 hlt))

/- English proof (translation)
Rewrite using `[norm_unit p v hv, one_pow]`. Conclude with `(PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := u)).2 hu`.
-/
private theorem padic_norm_lt_norm_sq_of_dvd_of_not_dvd (p : ℕ) [Fact p.Prime] (u v : ℤ) (hu : (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) : ‖(u : ℤ_[p])‖ < ‖(v : ℤ_[p])‖ ^ 2 := by
  rw [norm_unit p v hv, one_pow]
  exact (PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := u)).2 hu

/- English proof (translation)
Establish `: NeZero p` using `⟨hp.out.ne_zero⟩`. Establish `hcp : (c : ZMod p) ≠ 0` using `fun h => hc ((CharP.cast_eq_zero_iff (ZMod p) p c).1 h)`. Establish `hodd : Fintype.card (ZMod p) % 2 = 1`. Rewrite using `[ZMod.card]`. Conclude with `Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)`.

Take `⟨u, v, huv⟩` from `FiniteField.exists_root_sum_quadratic (f := X ^ 2 + C (1 : ZMod p)) (g := C (c : ZMod p) * X ^ 2) (by simpa using degree_X_pow_add_C (R := ZMod p) (n := 2) (by norm_num) 1) (by simpa using degree_C_mul_X_pow 2 hcp) hodd`. Take `⟨x₀, rfl⟩` from `ZMod.intCast_surjective u`. Take `⟨y₀, rfl⟩` from `ZMod.intCast_surjective v`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp.out`. Establish `h2 : ¬ (p : ℤ) ∣ 2`.

Introduce `h`. Establish `h' : p ∣ 2` using `by exact_mod_cast h`. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')`. Establish `hcz : ¬ (p : ℤ) ∣ (c : ℤ)` using `by exact_mod_cast hc`. Establish `hdiv : (p : ℤ) ∣ x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1`.

Rewrite using `[← CharP.intCast_eq_zero_iff (ZMod p) p]`. Simplify using `only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at huv`. Use `push_cast`. Take the linear combination `huv`. Distinguish the cases in `hx : (p : ℤ) ∣ x₀`.

Establish `hy : ¬ (p : ℤ) ∣ y₀`. Introduce `hy`. Establish `h1 : (p : ℤ) ∣ 1`. Establish `e : (1 : ℤ) = (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1) - (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2)` using `by ring`. Rewrite using `[e]`.

Conclude with `dvd_sub hdiv (dvd_add (dvd_pow hx two_ne_zero) (dvd_mul_of_dvd_right (dvd_pow hy two_ne_zero) (c : ℤ)))`. Conclude with `hpz.not_dvd_one h1`. Take `⟨z, hz⟩` from `hensel_quad p c (x₀ ^ 2 + 1) y₀ (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring) (fun h => (hpz.dvd_or_dvd h).elim (fun h => (hpz.dvd_or_dvd h).elim h2 hcz) hy))`. Conclude with `⟨x₀, z, by push_cast at hz; linear_combination hz⟩`. Take `⟨z, hz⟩` from `hensel_quad p 1 (c * y₀ ^ 2 + 1) x₀ (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring) (fun h => (hpz.dvd_or_dvd h).elim (fun h => (hpz.dvd_or_dvd h).elim h2 hpz.not_dvd_one) hx))`.

Conclude with `⟨z, y₀, by push_cast at hz; linear_combination hz⟩`.
-/
theorem rep_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) :
    ∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hcp : (c : ZMod p) ≠ 0 := fun h => hc ((CharP.cast_eq_zero_iff (ZMod p) p c).1 h)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  obtain ⟨u, v, huv⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2 + C (1 : ZMod p)) (g := C (c : ZMod p) * X ^ 2)
    (by simpa using degree_X_pow_add_C (R := ZMod p) (n := 2) (by norm_num) 1)
    (by simpa using degree_C_mul_X_pow 2 hcp) hodd
  obtain ⟨x₀, rfl⟩ := ZMod.intCast_surjective u
  obtain ⟨y₀, rfl⟩ := ZMod.intCast_surjective v
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')
  have hcz : ¬ (p : ℤ) ∣ (c : ℤ) := by exact_mod_cast hc
  have hdiv : (p : ℤ) ∣ x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1 := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at huv
    push_cast
    linear_combination huv
  by_cases hx : (p : ℤ) ∣ x₀
  · have hy : ¬ (p : ℤ) ∣ y₀ := by
      intro hy
      have h1 : (p : ℤ) ∣ 1 := by
        have e : (1 : ℤ) = (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1) - (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2) := by ring
        rw [e]
        exact dvd_sub hdiv (dvd_add (dvd_pow hx two_ne_zero)
          (dvd_mul_of_dvd_right (dvd_pow hy two_ne_zero) (c : ℤ)))
      exact hpz.not_dvd_one h1
    obtain ⟨z, hz⟩ := hensel_quad p c (x₀ ^ 2 + 1) y₀
      (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring)
        (fun h => (hpz.dvd_or_dvd h).elim (fun h => (hpz.dvd_or_dvd h).elim h2 hcz) hy))
    exact ⟨x₀, z, by push_cast at hz; linear_combination hz⟩
  · obtain ⟨z, hz⟩ := hensel_quad p 1 (c * y₀ ^ 2 + 1) x₀
      (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring)
        (fun h => (hpz.dvd_or_dvd h).elim
          (fun h => (hpz.dvd_or_dvd h).elim h2 hpz.not_dvd_one) hx))
    exact ⟨z, y₀, by push_cast at hz; linear_combination hz⟩

/- English proof (translation)
Establish `h8 : ((2 : ℕ) : ℤ) ^ 3 ∣ (c : ℤ) * 1 ^ 2 + 5` using `by norm_num; omega`. Establish `hc2 : ¬ ((2 : ℕ) : ℤ) ∣ (c : ℤ)` using `by push_cast; omega`. Establish `hB : ‖((2 * (c : ℤ) * 1 : ℤ) : ℤ_[2])‖ = 2⁻¹`. Rewrite using `[show (2 * (c : ℤ) * 1 : ℤ) = ((2 : ℕ) : ℤ) * c by push_cast; ring, Int.cast_mul, norm_mul, norm_unit 2 c hc2, Int.cast_natCast, PadicInt.norm_p]`. Evaluate the numerical expressions.

Take `⟨z, hz⟩` from `hensel_quad 2 c 5 1 (by`. Rewrite using `[hB]`. Use `lt_of_le_of_lt ((PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := (c : ℤ) * 1 ^ 2 + 5) (n := 3)).2 h8) ?_` and prove the remaining obligations. Evaluate the numerical expressions using `[zpow_neg])`. Conclude with `⟨2, z, by push_cast at hz; linear_combination hz⟩`.
-/
theorem rep_two (c : ℕ) (hc : c % 8 = 3) : ∃ x y : ℤ_[2], x ^ 2 + (c : ℤ_[2]) * y ^ 2 = -1 := by
  have h8 : ((2 : ℕ) : ℤ) ^ 3 ∣ (c : ℤ) * 1 ^ 2 + 5 := by
    norm_num; omega
  have hc2 : ¬ ((2 : ℕ) : ℤ) ∣ (c : ℤ) := by
    push_cast; omega
  have hB : ‖((2 * (c : ℤ) * 1 : ℤ) : ℤ_[2])‖ = 2⁻¹ := by
    rw [show (2 * (c : ℤ) * 1 : ℤ) = ((2 : ℕ) : ℤ) * c by push_cast; ring, Int.cast_mul, norm_mul,
      norm_unit 2 c hc2, Int.cast_natCast, PadicInt.norm_p]
    norm_num
  obtain ⟨z, hz⟩ := hensel_quad 2 c 5 1 (by
    rw [hB]
    refine lt_of_le_of_lt ((PadicInt.norm_int_le_pow_iff_dvd (p := 2)
      (k := (c : ℤ) * 1 ^ 2 + 5) (n := 3)).2 h8) ?_
    norm_num [zpow_neg])
  exact ⟨2, z, by push_cast at hz; linear_combination hz⟩

def Rep (q d m : ℕ) : Prop :=
  ∃ α β γ δ : ZMod m, (α ^ 2 + (q : ZMod m) * β ^ 2) * (γ ^ 2 + (d : ZMod m) * δ ^ 2) = -1

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `key : ∀ c : ℕ, (∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1) → ∃ α β : ZMod (p ^ k), α ^ 2 + (c : ZMod (p ^ k)) * β ^ 2 = -1`. Introduce and unpack `c ⟨x, y, h⟩`. Use `⟨PadicInt.toZModPow k x, PadicInt.toZModPow k y, ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (PadicInt.toZModPow (p := p) k) h`.

Break down `eq_or_ne p q with hpq | hpq` into its components or cases. Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Rewrite `hq8` using `[← hpq]`. Evaluate the numerical expressions using `at hq8`.

Establish `hpd : ¬ p ∣ d` using `fun h => hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 (by rwa [← hpq]))`. Take `⟨γ, δ, h⟩` from `key d (rep_odd p hp2 d hpd)`. Conclude with `⟨1, 0, γ, δ, by simp [h]⟩`. Break down `eq_or_ne p 2 with hp2 | hp2` into its components or cases. Substitute `hp2` using the available equality.

Take `⟨α, β, h⟩` from `key q (rep_two q hq8)`. Conclude with `⟨α, β, 1, 0, by simp [h]⟩`. Establish `hpq' : ¬ p ∣ q` using `fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)`. Take `⟨α, β, h⟩` from `key q (rep_odd p hp2 q hpq')`. Conclude with `⟨α, β, 1, 0, by simp [h]⟩`.
-/
theorem rep_pp (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (p k : ℕ) (hp : p.Prime) :
    Rep q d (p ^ k) := by
  have := Fact.mk hp
  have key : ∀ c : ℕ, (∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1) →
      ∃ α β : ZMod (p ^ k), α ^ 2 + (c : ZMod (p ^ k)) * β ^ 2 = -1 := by
    rintro c ⟨x, y, h⟩
    refine ⟨PadicInt.toZModPow k x, PadicInt.toZModPow k y, ?_⟩
    simpa using congrArg (PadicInt.toZModPow (p := p) k) h
  rcases eq_or_ne p q with hpq | hpq
  · have hp2 : p ≠ 2 := by
      rintro rfl; rw [← hpq] at hq8; norm_num at hq8
    have hpd : ¬ p ∣ d := fun h =>
      hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 (by rwa [← hpq]))
    obtain ⟨γ, δ, h⟩ := key d (rep_odd p hp2 d hpd)
    exact ⟨1, 0, γ, δ, by simp [h]⟩
  · rcases eq_or_ne p 2 with hp2 | hp2
    · subst hp2
      obtain ⟨α, β, h⟩ := key q (rep_two q hq8)
      exact ⟨α, β, 1, 0, by simp [h]⟩
    · have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
      obtain ⟨α, β, h⟩ := key q (rep_odd p hp2 q hpq')
      exact ⟨α, β, 1, 0, by simp [h]⟩

/- English proof (translation)
Take `⟨α₁, β₁, γ₁, δ₁, h₁⟩` from `ha`. Take `⟨α₂, β₂, γ₂, δ₂, h₂⟩` from `hb`. Set `e` to `ZMod.chineseRemainder hab`. Use `⟨e.symm (α₁, α₂), e.symm (β₁, β₂), e.symm (γ₁, γ₂), e.symm (δ₁, δ₂), e.injective ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_add, map_pow, map_natCast, map_neg, map_one, RingEquiv.apply_symm_apply]`.

Apply the tactic sequence `ext <;> simp [h₁, h₂]`.
-/
private theorem rep_mul_of_coprime {q d a b : ℕ} (hab : Nat.Coprime a b)
    (ha : Rep q d a) (hb : Rep q d b) :
    Rep q d (a * b) := by
  obtain ⟨α₁, β₁, γ₁, δ₁, h₁⟩ := ha
  obtain ⟨α₂, β₂, γ₂, δ₂, h₂⟩ := hb
  let e := ZMod.chineseRemainder hab
  refine ⟨e.symm (α₁, α₂), e.symm (β₁, β₂), e.symm (γ₁, γ₂), e.symm (δ₁, δ₂), e.injective ?_⟩
  simp only [map_mul, map_add, map_pow, map_natCast, map_neg, map_one,
    RingEquiv.apply_symm_apply]
  ext <;> simp [h₁, h₂]

/- English proof (translation)
Proceed by induction on `m using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p n hp _ => exact fun _ => rep_pp q d hq hd hq8 hqd p n hp`. Consider the case `zero => exact fun h => absurd h (lt_irrefl 0)`. Consider the case `one`. Introduce `_`.

Simplify using `using rep_pp q d hq hd hq8 hqd 2 0 Nat.prime_two`. Consider the case `coprime a b ha1 hb1 hab ha hb`. Conclude with `fun _ => rep_mul_of_coprime hab (ha (by omega)) (hb (by omega))`.
-/
theorem rep_all (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) :
    0 < m → Rep q d m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact fun _ => rep_pp q d hq hd hq8 hqd p n hp
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | one =>
    intro _
    simpa using rep_pp q d hq hd hq8 hqd 2 0 Nat.prime_two
  | coprime a b ha1 hb1 hab ha hb =>
    exact fun _ => rep_mul_of_coprime hab (ha (by omega)) (hb (by omega))

/- English proof (translation)
Take `⟨α, β, γ, δ, h⟩` from `rep_all q d hq hd hq8 hqd m hm`. Take `⟨a, rfl⟩` from `ZMod.intCast_surjective α`. Take `⟨b, rfl⟩` from `ZMod.intCast_surjective β`. Take `⟨c, rfl⟩` from `ZMod.intCast_surjective γ`. Take `⟨e, rfl⟩` from `ZMod.intCast_surjective δ`.

Establish `hdvd : (m : ℤ) ∣ (a ^ 2 + q * b ^ 2) * (c ^ 2 + d * e ^ 2) + 1`. Rewrite using `[← CharP.intCast_eq_zero_iff (ZMod m) m]`. Use `push_cast`. Take the linear combination `h`. Take `⟨s, hs⟩` from `hdvd`.

Conclude with `⟨a, b, c, e, s, by linear_combination hs⟩`.
-/
theorem rep_int (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) (hm : 0 < m) :
    ∃ α β γ δ s : ℤ, (α ^ 2 + q * β ^ 2) * (γ ^ 2 + d * δ ^ 2) = -1 + m * s := by
  obtain ⟨α, β, γ, δ, h⟩ := rep_all q d hq hd hq8 hqd m hm
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective α
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective β
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective γ
  obtain ⟨e, rfl⟩ := ZMod.intCast_surjective δ
  have hdvd : (m : ℤ) ∣ (a ^ 2 + q * b ^ 2) * (c ^ 2 + d * e ^ 2) + 1 := by
    rw [← CharP.intCast_eq_zero_iff (ZMod m) m]
    push_cast
    linear_combination h
  obtain ⟨s, hs⟩ := hdvd
  exact ⟨a, b, c, e, s, by linear_combination hs⟩

end Formalism.L2.PairingIndexBounds.Eq.J.Neg
