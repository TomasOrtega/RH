import Mathlib

namespace CoprimeTimesDvdPowFactorization

/- English proof (translation)
Use `set d := Nat.gcd m (g ^ m) with hd`. Establish `hdpos : 0 < d` using `Nat.gcd_pos_of_pos_left _ hm`. Establish `hcop : (m / d).Coprime (g ^ m / d)` using `Nat.coprime_div_gcd_div_gcd hdpos`. Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `p hp hpc hpg`.

Establish `hpn : ¬ p ∣ g ^ m / d`. Introduce `h`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpc hcop) h`. Establish `hdg : d ∣ g ^ m` using `Nat.gcd_dvd_right _ _`. Establish `hdm : d ∣ m` using `Nat.gcd_dvd_left _ _`.

Establish `hpm : p ^ m ∣ d * (g ^ m / d)`. Rewrite using `[Nat.mul_div_cancel' hdg]`. Conclude with `pow_dvd_pow_of_dvd hpg m`. Establish `hcp : Nat.Coprime (p ^ m) (g ^ m / d)` using `Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)`. Establish `hpd : p ^ m ∣ d` using `hcp.dvd_of_dvd_mul_right hpm`.

Establish `hall : p ^ m * p ∣ d * (m / d)` using `Nat.mul_dvd_mul hpd hpc`. Rewrite `hall` using `[Nat.mul_div_cancel' hdm, ← pow_succ]`. Establish `hle : p ^ (m + 1) ≤ m` using `Nat.le_of_dvd hm hall`. Establish `h1 : m < 2 ^ m` using `Nat.lt_two_pow_self`. Establish `h2 : 2 ^ m ≤ p ^ m` using `Nat.pow_le_pow_left hp.two_le m`.

Establish `h3 : p ^ m ≤ p ^ (m + 1)` using `Nat.pow_le_pow_right hp.pos (Nat.le_succ m)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem key (g m : ℕ) (hm : 0 < m) :
    (m / Nat.gcd m (g ^ m)).Coprime g := by
  set d := Nat.gcd m (g ^ m) with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hm
  have hcop : (m / d).Coprime (g ^ m / d) := Nat.coprime_div_gcd_div_gcd hdpos
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  have hpn : ¬ p ∣ g ^ m / d := by
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpc hcop) h
  have hdg : d ∣ g ^ m := Nat.gcd_dvd_right _ _
  have hdm : d ∣ m := Nat.gcd_dvd_left _ _
  have hpm : p ^ m ∣ d * (g ^ m / d) := by
    rw [Nat.mul_div_cancel' hdg]
    exact pow_dvd_pow_of_dvd hpg m
  have hcp : Nat.Coprime (p ^ m) (g ^ m / d) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
  have hpd : p ^ m ∣ d := hcp.dvd_of_dvd_mul_right hpm
  have hall : p ^ m * p ∣ d * (m / d) := Nat.mul_dvd_mul hpd hpc
  rw [Nat.mul_div_cancel' hdm, ← pow_succ] at hall
  have hle : p ^ (m + 1) ≤ m := Nat.le_of_dvd hm hall
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
  have h3 : p ^ m ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ m)
  omega

end CoprimeTimesDvdPowFactorization

/- English proof (translation)
Introduce `g m hm`. Use `⟨m / Nat.gcd m (g ^ m), Nat.gcd m (g ^ m), ?_, CoprimeTimesDvdPowFactorization.key g m hm, Nat.gcd_dvd_right _ _⟩` and prove the remaining obligations. Conclude with `(Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm`.
-/
theorem UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main :
    ∀ (g m : ℕ),
    (0 : ℕ) < m → ∃ (c : ℕ) (d : ℕ), m = c * d ∧ c.Coprime g ∧ d ∣ g ^ m := by
  intro g m hm
  refine ⟨m / Nat.gcd m (g ^ m), Nat.gcd m (g ^ m), ?_, CoprimeTimesDvdPowFactorization.key g m hm, Nat.gcd_dvd_right _ _⟩
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
