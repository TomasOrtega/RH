import Mathlib

namespace Bl.SecondBlockLemmaL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] (ℓ : Nat) [hℓ : Fact (Nat.Prime ℓ)]
  {Q : Ideal.{0} (NumberField.RingOfIntegers.{0} E)},
  Ideal.IsPrime.{0} Q →
    Ne.{1} Q Bot.bot.{0} →
      Not (Membership.mem.{0, 0} Q (Nat.cast.{0} ℓ)) →
        Eq.{1} (padicValNat ℓ (DFunLike.coe.{1, 1, 1} Ideal.absNorm.{0} Q)) 0 := by
  intro E _ _ ℓ hℓ Q hQ hne hmem
  have h0 : Ideal.absNorm Q ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  have hfin : Finite (NumberField.RingOfIntegers E ⧸ Q) := (Ideal.absNorm_ne_zero_iff Q).mp h0
  rw [padicValNat.eq_zero_iff]
  refine Or.inr (Or.inr ?_)
  intro hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ hdvd
  have h1 := addOrderOf_nsmul_eq_zero x
  rw [hx, nsmul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · apply hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact h
  · have h2 : addOrderOf x = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr h
    exact hℓ.out.ne_one (hx ▸ h2)

end Bl.SecondBlockLemmaL
