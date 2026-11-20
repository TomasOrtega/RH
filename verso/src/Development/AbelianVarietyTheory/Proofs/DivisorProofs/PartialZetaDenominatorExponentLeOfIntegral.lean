import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.DenomBound

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem cE_le_of_inZl : ∀ {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime], 2 ≤ a → 1 ≤ n →
    (∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) → cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) := by
  intro F _ _ z l a n _ ha hn h
  unfold cE
  apply Finset.sup_le
  intro C _
  unfold denomExp
  by_cases hz : z C = 0
  · simp [hz]
  have hpow : 2 ≤ a ^ n := le_trans ha (Nat.le_self_pow (by omega) a)
  have hA : (a ^ n - 1 : ℕ) ≠ 0 := by omega
  have hAq : ((a ^ n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hA
  have h1 := h C
  rw [inZl_iff, padicValRat.mul hAq hz, padicValRat.of_nat] at h1
  have h2 : (2 : ℚ) ^ finrank ℚ F ≠ 0 := pow_ne_zero _ two_ne_zero
  have h3 : padicValRat l (z C / 2 ^ finrank ℚ F) = padicValRat l (z C) - (finrank ℚ F : ℤ) * (padicValNat l 2 : ℤ) := by
    rw [padicValRat.div hz h2, padicValRat.pow (q := (2:ℚ))]
    have : padicValRat l (2 : ℚ) = padicValNat l 2 := by
      have := padicValRat.of_nat (p := l) (n := 2)
      simpa using this
    rw [this]
  rw [h3]
  omega

end GlobalTheory.DenomBound
