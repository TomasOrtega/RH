import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

namespace GlobalTheory.NormDivisibility

open NumberField IsDedekindDomain

/- English proof (translation)
Use `Fintype.ofFinite R` as an intermediate fact. Set `_ : Field R` to `Fintype.fieldOfDomain R`. Take `⟨n, hp, hc⟩` from `FiniteField.card R (ringChar R)`. Rewrite `h` using `[Nat.card_eq_fintype_card, hc]`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]`.

Conclude with `ringChar.Nat.cast_ringChar`.
-/
theorem natCast_eq_zero_of_dvd_card {R : Type*} [CommRing R] [IsDomain R] [Finite R] {l : ℕ}
    (hl : l.Prime) (h : l ∣ Nat.card R) : (l : R) = 0 := by
  classical
  have := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R

  obtain ⟨n, hp, hc⟩ := FiniteField.card R (ringChar R)
  rw [Nat.card_eq_fintype_card, hc] at h
  rw [(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]
  exact ringChar.Nat.cast_ringChar

/- English proof (translation)
Introduce `h`. Establish `: Finite (RingOfIntegers E ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Unfold `Formalism.ConjugateSelfDual.normV at h`. Establish `h0` using `natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h0`.
-/
theorem not_dvd_norm_of_not_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : Nat.Prime l)
    (w : HeightOneSpectrum (RingOfIntegers E))
    (hw : (l : RingOfIntegers E) ∉ w.asIdeal) : ¬ l ∣ Formalism.ConjugateSelfDual.normV w := by
  intro h
  have : Finite (RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  unfold Formalism.ConjugateSelfDual.normV at h
  have h0 := natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

end GlobalTheory.NormDivisibility
