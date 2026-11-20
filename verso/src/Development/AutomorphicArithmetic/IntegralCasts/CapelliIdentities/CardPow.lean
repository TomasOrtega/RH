import Mathlib

/- English proof (translation)
Introduce `E _ _ w q hq hmem`. Use `haveI : w.asIdeal.IsMaximal := w.isMaximal`. Use `haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Use `letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal`. Use `letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _`.

Establish `h0 : (q : NumberField.RingOfIntegers E ⧸ w.asIdeal) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.mpr hmem` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `haveI : CharP (NumberField.RingOfIntegers E ⧸ w.asIdeal) q := (CharP.charP_iff_prime_eq_zero (p := q) (hp := hq)).mpr h0`. Take `⟨n, -, hn⟩` from `FiniteField.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) q`.

Conclude with `⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩`.
-/
theorem UpperTheory.Reformulated.B.Qi54.card_pow :
    ∀ {E : Type} [inst : Field E] [NumberField E]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (q : ℕ),
    Nat.Prime q →
      (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal →
        ∃ (f : ℕ), Nat.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) = q ^ f := by
  intro E _ _ w q hq hmem
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have h0 : (q : NumberField.RingOfIntegers E ⧸ w.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (NumberField.RingOfIntegers E ⧸ w.asIdeal) q :=
    (CharP.charP_iff_prime_eq_zero (p := q) (hp := hq)).mpr h0
  obtain ⟨n, -, hn⟩ := FiniteField.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) q
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
