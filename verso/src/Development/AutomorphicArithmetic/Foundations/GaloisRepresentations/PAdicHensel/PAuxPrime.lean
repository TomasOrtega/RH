import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

/- English proof (translation)
Establish `hp : (p : ℤ) ∣ ((m ^ 2 + d : ℕ) : ℤ)` using `by exact_mod_cast h1`. Establish `hq : ¬ (p : ℤ) ∣ ((2 * m : ℕ) : ℤ)` using `by exact_mod_cast h2`. Use `set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p]) with hF`. Use `set a : ℤ_[p] := ((m : ℤ) : ℤ_[p]) with ha`. Establish `e1 : Polynomial.aeval a F = (((m ^ 2 + d : ℕ) : ℤ) : ℤ_[p])`.

Simplify using `[hF, ha]`. Establish `e2 : Polynomial.aeval a (Polynomial.derivative F) = (((2 * m : ℕ) : ℤ) : ℤ_[p])`. Simplify using `[hF, ha]`. Use `left`. Evaluate the numerical expressions.

Establish `n1 : ‖Polynomial.aeval a F‖ < 1`. Rewrite using `[e1]`. Conclude with `(PadicInt.norm_int_lt_one_iff_dvd _).2 hp`. Establish `n2 : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1`. Rewrite using `[e2]`.

Conclude with `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hq ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))`. Take `⟨z, hz, -⟩` from `hensels_lemma (F := F) (a := a) (by rw [n2]; simpa using n1)`. Establish `hz' : z ^ 2 + (d : ℤ_[p]) = 0` using `by simpa [hF] using hz`. Establish `hz'' : ((z : ℚ_[p])) ^ 2 + (d : ℚ_[p]) = 0`. Use `congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz'` as an intermediate fact.

Simplify using `using this`. Use `⟨(z : ℚ_[p]), ?_⟩` and prove the remaining obligations. Take the linear combination `-hz''`.
-/
private theorem sq_of_dvd (p : ℕ) [Fact p.Prime] (d m : ℕ) (h1 : p ∣ m ^ 2 + d) (h2 : ¬ p ∣ 2 * m) :
    IsSquare (-(d : ℚ_[p])) := by
  have hp : (p : ℤ) ∣ ((m ^ 2 + d : ℕ) : ℤ) := by exact_mod_cast h1
  have hq : ¬ (p : ℤ) ∣ ((2 * m : ℕ) : ℤ) := by exact_mod_cast h2
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p]) with hF
  set a : ℤ_[p] := ((m : ℤ) : ℤ_[p]) with ha
  have e1 : Polynomial.aeval a F = (((m ^ 2 + d : ℕ) : ℤ) : ℤ_[p]) := by
    simp [hF, ha]
  have e2 : Polynomial.aeval a (Polynomial.derivative F) = (((2 * m : ℕ) : ℤ) : ℤ_[p]) := by
    simp [hF, ha]
    left
    norm_num
  have n1 : ‖Polynomial.aeval a F‖ < 1 := by
    rw [e1]; exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hp
  have n2 : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [e2]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.1 fun h => hq ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [n2]; simpa using n1)
  have hz' : z ^ 2 + (d : ℤ_[p]) = 0 := by simpa [hF] using hz
  have hz'' : ((z : ℚ_[p])) ^ 2 + (d : ℚ_[p]) = 0 := by
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz'
    simpa using this
  refine ⟨(z : ℚ_[p]), ?_⟩
  linear_combination -hz''

/- English proof (translation)
Introduce `d hd b`. Use `set c := (max b (2 * d)).factorial with hc`. Establish `hcpos : 0 < c` using `Nat.factorial_pos _`. Establish `hN : d * c ^ 2 + 1 ≠ 1`. Establish `: 0 < d * c ^ 2` using `by positivity`.

Use linear arithmetic over natural numbers and integers. Take `⟨p, hp, hdvd⟩` from `Nat.exists_prime_and_dvd hN`. Establish `hpc : ¬ p ∣ c` using `fun h => by`. Establish `h2 : p ∣ d * c ^ 2` using `Dvd.dvd.mul_left (dvd_pow h (by norm_num)) d`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 hdvd))`.

Establish `hgt : max b (2 * d) < p`. Assume the negation of the conclusion as `h`. Conclude with `hpc ((hp.dvd_factorial).2 (not_lt.1 h))`. Establish `hb : b < p` using `lt_of_le_of_lt (le_max_left _ _) hgt`. Establish `h2d : 2 * d < p` using `lt_of_le_of_lt (le_max_right _ _) hgt`.

Establish `hpd : ¬ p ∣ d` using `fun h => by`. Use `Nat.le_of_dvd hd h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hp2 : ¬ p ∣ 2` using `fun h => by`. Use `Nat.le_of_dvd (by norm_num) h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `⟨p, inferInstance, hb, sq_of_dvd p d (d * c) ?_ ?_⟩` and prove the remaining obligations. Establish `: (d * c) ^ 2 + d = d * (d * c ^ 2 + 1)` using `by ring`. Rewrite using `[this]`.

Conclude with `Dvd.dvd.mul_left hdvd d`. Introduce `h`. Break down `(Nat.Prime.dvd_mul hp).1 h with h | h` into its components or cases. Conclude with `hp2 h`. Break down `(Nat.Prime.dvd_mul hp).1 h with h | h` into its components or cases.

Conclude with `hpd h`. Conclude with `hpc h`.
-/
theorem UpperTheory.Gal.G1.exists_auxiliary_prime_cmDatum :
    AuxiliaryInertOddPrime := by
  intro d hd b
  set c := (max b (2 * d)).factorial with hc
  have hcpos : 0 < c := Nat.factorial_pos _
  have hN : d * c ^ 2 + 1 ≠ 1 := by
    have : 0 < d * c ^ 2 := by positivity
    omega
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hN
  have hpc : ¬ p ∣ c := fun h => by
    have h2 : p ∣ d * c ^ 2 := Dvd.dvd.mul_left (dvd_pow h (by norm_num)) d
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 hdvd))
  have hgt : max b (2 * d) < p := by
    by_contra h
    exact hpc ((hp.dvd_factorial).2 (not_lt.1 h))
  have hb : b < p := lt_of_le_of_lt (le_max_left _ _) hgt
  have h2d : 2 * d < p := lt_of_le_of_lt (le_max_right _ _) hgt
  have hpd : ¬ p ∣ d := fun h => by
    have := Nat.le_of_dvd hd h
    omega
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, inferInstance, hb, sq_of_dvd p d (d * c) ?_ ?_⟩
  · have : (d * c) ^ 2 + d = d * (d * c ^ 2 + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hdvd d
  · intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hpd h
      · exact hpc h
