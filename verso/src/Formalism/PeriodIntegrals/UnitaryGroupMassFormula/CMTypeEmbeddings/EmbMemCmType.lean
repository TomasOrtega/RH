import Formalism.PeriodIntegrals.EtaHostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

open NumberField Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace PI.HostPsiFactsWork

variable {R : Ranks}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem galE_sigmaOf (H : Host R) (g : R.GG) :
    H.galE (H.sigmaOf g) = g :=
  show H.gal ((H.gal).symm g) = g from
    MulEquiv.apply_symm_apply _ _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem emb_mem_cmType (H : Host R) (g : R.GG) (hg : g ∈ R.Psi) :
    H.emb g ∈ H.cmType := by
  have key := H.der.cmType.2.2
    H.φ₀ H.φ₀_mem (H.sigmaOf g)
  exact key.2 (by
    have e : H.gal (H.sigmaOf g) = g := galE_sigmaOf H g
    rw [e]; exact hg)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem card4 : PI.EtaHostFacts.Card4 := by
  intro hc R H
  rw [Fintype.card_eq_nat_card, (hc R H).1]
  have h4 : 4 ∣ 2 ^ R.e := (show (2 : ℕ) ^ 2 ∣ 2 ^ R.e from pow_dvd_pow 2 H.two_le_e)
  have h5 : 2 ^ R.e ∣ R.ord := R.toFrame.two_pow_dvd_ord
  exact (h4.trans h5).mul_left 2

end PI.HostPsiFactsWork
