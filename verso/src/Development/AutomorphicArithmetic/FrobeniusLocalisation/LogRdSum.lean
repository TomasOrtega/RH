import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Introduce `φ H`. Establish `hd : discr H.E ≠ 0` using `discr_ne_zero H.E`. Establish `hd' : (discr H.E).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 hd`. Establish `habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ)`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`.

Establish `hpos : 0 < |(discr H.E : ℝ)|` using `abs_pos.2 (Int.cast_ne_zero.2 hd)`. Establish `h1 : Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l`. Unfold `HostRaw.rd HostRaw.ram HostRaw.vdH`. Rewrite using `[Real.log_rpow hpos, habs, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations.

Rewrite using `[Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : H.ram ⊆ H.condN.primeFactors`. Introduce `l hl`. Establish `h` using `Nat.mem_primeFactors.1 hl`.

Conclude with `Nat.mem_primeFactors.2 ⟨h.1, H.der.discr_primes.1 l h.1 (Int.natCast_dvd.2 h.2.1), H.condN_ne_zero⟩`. Use `⟨h1, ?_, h3, Real.rpow_pos_of_pos hpos _⟩` and prove the remaining obligations. Rewrite using `[h1]`. Use `Finset.sum_subset h3 fun l hl hn => ?_` and prove the remaining obligations. Establish `hp` using `Nat.prime_of_mem_primeFactors hl`.

Establish `: ¬ l ∣ (discr H.E).natAbs` using `fun h => hn (Nat.mem_primeFactors.2 ⟨hp, h, hd'⟩)`. Unfold `HostRaw.vdH`. Rewrite using `[padicValNat.eq_zero_of_not_dvd this]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.HF.log_rd_sum :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l ∧ Real.log H.rd = ∑ l ∈ H.condN.primeFactors, H.vdH l * Real.log l ∧ H.ram ⊆ H.condN.primeFactors ∧ 0 < H.rd := by
  intro φ H
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have h1 : Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l := by
    unfold HostRaw.rd HostRaw.ram HostRaw.vdH
    rw [Real.log_rpow hpos, habs, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
    ring
  have h3 : H.ram ⊆ H.condN.primeFactors := by
    intro l hl
    have h := Nat.mem_primeFactors.1 hl
    exact Nat.mem_primeFactors.2 ⟨h.1, H.der.discr_primes.1 l h.1 (Int.natCast_dvd.2 h.2.1), H.condN_ne_zero⟩
  refine ⟨h1, ?_, h3, Real.rpow_pos_of_pos hpos _⟩
  rw [h1]
  refine Finset.sum_subset h3 fun l hl hn => ?_
  have hp := Nat.prime_of_mem_primeFactors hl
  have : ¬ l ∣ (discr H.E).natAbs := fun h => hn (Nat.mem_primeFactors.2 ⟨hp, h, hd'⟩)
  unfold HostRaw.vdH
  rw [padicValNat.eq_zero_of_not_dvd this]
  simp
