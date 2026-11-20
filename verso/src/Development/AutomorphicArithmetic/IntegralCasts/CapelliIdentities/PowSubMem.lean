import Mathlib

/- English proof (translation)
Introduce `E _ _ w x`. Use `haveI : w.asIdeal.IsMaximal := w.isMaximal`. Use `letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal`. Use `haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Use `letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _`.

Establish `hcard : Ideal.absNorm w.asIdeal = Fintype.card (NumberField.RingOfIntegers E ⧸ w.asIdeal)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Rewrite using `[← Ideal.Quotient.eq, map_pow, hcard]`. Conclude with `FiniteField.pow_card _`.
-/
theorem UpperTheory.Reformulated.B.Qk67.pow_sub_mem :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (x : NumberField.RingOfIntegers E),
    x ^ (Ideal.absNorm : Ideal (NumberField.RingOfIntegers E) → ℕ) w.asIdeal - x ∈ w.asIdeal := by
  intro E _ _ w x
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Ideal.absNorm w.asIdeal
      = Fintype.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← Ideal.Quotient.eq, map_pow, hcard]
  exact FiniteField.pow_card _
