import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qk10.exists_w :
    ∀ (K : Type) [inst : Field K] [NumberField K] {p : ℕ},
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (↑p : NumberField.RingOfIntegers K) ∈ w.asIdeal := by
  intro K _ _ p hp
  have hnu : ¬ IsUnit (p : NumberField.RingOfIntegers K) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ)) := by
      simpa using h
    have h2 : IsUnit (p : ℤ) := (isUnit_map_iff _ _).mp h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {(p : NumberField.RingOfIntegers K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : NumberField.RingOfIntegers K) ∈ M :=
    hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
