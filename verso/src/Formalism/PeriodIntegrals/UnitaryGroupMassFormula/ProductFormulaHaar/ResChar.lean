import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff

noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE.ResCharP

/- English proof (translation)
Introduce `F _ _ p ℓ hℓ`. Use `show ringChar (𝓞 F ⧸ p.asIdeal) = ℓ ↔ _`. Use `haveI : p.asIdeal.IsPrime := p.isPrime`. Establish `hz : ((ℓ : 𝓞 F ⧸ p.asIdeal) = 0) ↔ (ℓ : 𝓞 F) ∈ p.asIdeal`. Rewrite using `[← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`.

Rewrite using `[← hz]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← h]`. Conclude with `ringChar.Nat.cast_ringChar`.

Introduce `h`. Break down `hℓ.eq_one_or_self_of_dvd _ (ringChar.dvd h) with h1 | h1` into its components or cases. It suffices to derive a contradiction. Establish `hc` using `ringChar.Nat.cast_ringChar (R := 𝓞 F ⧸ p.asIdeal)`. Rewrite `hc` using `[h1, Nat.cast_one]`.

Conclude with `one_ne_zero hc`. Conclude with `h1`.
-/
theorem eq_iff_mem_asIdeal : St.ResCharIff := by
  intro F _ _ p ℓ hℓ
  show ringChar (𝓞 F ⧸ p.asIdeal) = ℓ ↔ _
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hz : ((ℓ : 𝓞 F ⧸ p.asIdeal) = 0) ↔ (ℓ : 𝓞 F) ∈ p.asIdeal := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  rw [← hz]
  constructor
  · intro h
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  · intro h
    rcases hℓ.eq_one_or_self_of_dvd _ (ringChar.dvd h) with h1 | h1
    · exfalso
      have hc := ringChar.Nat.cast_ringChar (R := 𝓞 F ⧸ p.asIdeal)
      rw [h1, Nat.cast_one] at hc
      exact one_ne_zero hc
    · exact h1

end PI.ProdFormulaE.ResCharP
