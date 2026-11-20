import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe49.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

/- English proof (translation)
Introduce `E _ _ w`. Use `haveI : w.asIdeal.IsPrime := w.isPrime`. Use `haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Use `⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal), CharP.prime_ringChar _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Conclude with `ringChar.Nat.cast_ringChar`.
-/
theorem UpperTheory.Reformulated.B.Qe49.exists_prime_mem :
    ∀ {E : Type} [inst : Field E] [NumberField E] (w : UpperTheory.Reformulated.B.Qe49.Plc E),
      ∃ (q : ℕ), Nat.Prime q ∧ (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ w
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal),
    CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar
