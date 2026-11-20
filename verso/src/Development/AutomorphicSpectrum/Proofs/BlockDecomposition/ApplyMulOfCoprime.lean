import Mathlib

namespace GlobalTheory.CompanionTheory.HeckeMult

variable {R : Type*} [CommRing R]

/- English proof (translation)
Proceed by induction on `j using Nat.twoStepInduction with`. Consider the case `zero => simp [h1]`. Consider the case `one => simpa using hcop p hp n hn hpn`. Consider the case `more j ih0 ih1`. Establish `hpj : 0 < p ^ j` using `pow_pos hp.pos j`.

Establish `e1 : p ^ (j + 2) * n = p * (p * (p ^ j * n))` using `by ring`. Establish `e2 : p ^ (j + 2) = p * (p * (p ^ j * 1))` using `by ring`. Establish `e3 : p ^ (j + 1) * n = p * (p ^ j * n)` using `by ring`. Establish `e4 : p ^ (j + 1) = p * (p ^ j * 1)` using `by ring`. Establish `r1` using `hrec p hp (p ^ j * n) (Nat.mul_pos hpj hn)`.

Establish `r2` using `hrec p hp (p ^ j * 1) (by simpa using hpj)`. Rewrite `ih1` using `[e3]`. Rewrite using `[e1, r1, ih1, ih0]`. Rewrite using `[e2, r2]`. Rewrite using `[← e4, mul_one]`.

Rewrite using `[e4, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem apply_prime_pow_mul (a c : ℕ → R) (h1 : a 1 = 1)
    (hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n)
    (hrec : ∀ p, p.Prime → ∀ n, 0 < n → a (p * (p * n)) = a p * a (p * n) - c p * a n)
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hpn : ¬ p ∣ n) (j : ℕ) :
    a (p ^ j * n) = a (p ^ j) * a n := by
  induction j using Nat.twoStepInduction with
  | zero => simp [h1]
  | one => simpa using hcop p hp n hn hpn
  | more j ih0 ih1 =>
    have hpj : 0 < p ^ j := pow_pos hp.pos j
    have e1 : p ^ (j + 2) * n = p * (p * (p ^ j * n)) := by ring
    have e2 : p ^ (j + 2) = p * (p * (p ^ j * 1)) := by ring
    have e3 : p ^ (j + 1) * n = p * (p ^ j * n) := by ring
    have e4 : p ^ (j + 1) = p * (p ^ j * 1) := by ring
    have r1 := hrec p hp (p ^ j * n) (Nat.mul_pos hpj hn)
    have r2 := hrec p hp (p ^ j * 1) (by simpa using hpj)
    rw [e3] at ih1
    rw [e1, r1, ih1, ih0]
    rw [e2, r2]
    rw [← e4, mul_one]
    rw [e4, mul_one]
    ring

/- English proof (translation)
Proceed by induction on `m using Nat.recOnPosPrimePosCoprime generalizing n with`. Consider the case `prime_pow p k hp hk`. Establish `hpn : ¬ p ∣ n` using `fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk.ne') hmn) dvd_rfl h)`. Establish `hn : 0 < n` using `Nat.pos_of_ne_zero fun h => hpn (h ▸ dvd_zero p)`. Conclude with `apply_prime_pow_mul a c h1 hcop hrec hp hn hpn k`.

Consider the case `zero`. Establish `: n = 1` using `by simpa using hmn`. Substitute `this` using the available equality. Simplify using `[h1]`. Consider the case `one => simp [h1]`.

Consider the case `coprime x y _ _ hxy ihx ihy`. Establish `hx : Nat.Coprime x n` using `Nat.Coprime.coprime_dvd_left (dvd_mul_right x y) hmn`. Establish `hy : Nat.Coprime y n` using `Nat.Coprime.coprime_dvd_left (dvd_mul_left y x) hmn`. Rewrite using `[mul_assoc, ihx _ (Nat.Coprime.mul_right hxy hx), ihy _ hy, ihx _ hxy, mul_assoc]`.
-/
theorem apply_mul_of_coprime (a c : ℕ → R) (h1 : a 1 = 1)
    (hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n)
    (hrec : ∀ p, p.Prime → ∀ n, 0 < n → a (p * (p * n)) = a p * a (p * n) - c p * a n)
    (m n : ℕ) (hmn : Nat.Coprime m n) : a (m * n) = a m * a n := by
  induction m using Nat.recOnPosPrimePosCoprime generalizing n with
  | prime_pow p k hp hk =>
    have hpn : ¬ p ∣ n := fun h =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk.ne') hmn) dvd_rfl h)
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => hpn (h ▸ dvd_zero p)
    exact apply_prime_pow_mul a c h1 hcop hrec hp hn hpn k
  | zero =>
    have : n = 1 := by simpa using hmn
    subst this
    simp [h1]
  | one => simp [h1]
  | coprime x y _ _ hxy ihx ihy =>
    have hx : Nat.Coprime x n := Nat.Coprime.coprime_dvd_left (dvd_mul_right x y) hmn
    have hy : Nat.Coprime y n := Nat.Coprime.coprime_dvd_left (dvd_mul_left y x) hmn
    rw [mul_assoc, ihx _ (Nat.Coprime.mul_right hxy hx), ihy _ hy, ihx _ hxy, mul_assoc]

end GlobalTheory.CompanionTheory.HeckeMult
