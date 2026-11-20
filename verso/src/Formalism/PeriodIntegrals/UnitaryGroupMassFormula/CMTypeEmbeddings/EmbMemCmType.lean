import Formalism.PeriodIntegrals.EtaHostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

open NumberField Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace PI.HostPsiFactsWork

variable {R : Ranks}

/- English proof (translation)
The claim follows from `show H.gal ((H.gal).symm g) = g from MulEquiv.apply_symm_apply _ _`.
-/
theorem galE_sigmaOf (H : Host R) (g : R.GG) :
    H.galE (H.sigmaOf g) = g :=
  show H.gal ((H.gal).symm g) = g from
    MulEquiv.apply_symm_apply _ _

/- English proof (translation)
Establish `key` using `H.der.cmType.2.2 H.φ₀ H.φ₀_mem (H.sigmaOf g)`. Conclude with `key.2 (by`. Establish `e : H.gal (H.sigmaOf g) = g` using `galE_sigmaOf H g`. Rewrite using `[e]`. Conclude with `hg)`.
-/
theorem emb_mem_cmType (H : Host R) (g : R.GG) (hg : g ∈ R.Psi) :
    H.emb g ∈ H.cmType := by
  have key := H.der.cmType.2.2
    H.φ₀ H.φ₀_mem (H.sigmaOf g)
  exact key.2 (by
    have e : H.gal (H.sigmaOf g) = g := galE_sigmaOf H g
    rw [e]; exact hg)

/- English proof (translation)
Introduce `hc R H`. Rewrite using `[Fintype.card_eq_nat_card, (hc R H).1]`. Establish `h4 : 4 ∣ 2 ^ R.e` using `(show (2 : ℕ) ^ 2 ∣ 2 ^ R.e from pow_dvd_pow 2 H.two_le_e)`. Establish `h5 : 2 ^ R.e ∣ R.ord` using `R.toFrame.two_pow_dvd_ord`. Conclude with `(h4.trans h5).mul_left 2`.
-/
theorem card4 : PI.EtaHostFacts.Card4 := by
  intro hc R H
  rw [Fintype.card_eq_nat_card, (hc R H).1]
  have h4 : 4 ∣ 2 ^ R.e := (show (2 : ℕ) ^ 2 ∣ 2 ^ R.e from pow_dvd_pow 2 H.two_le_e)
  have h5 : 2 ^ R.e ∣ R.ord := R.toFrame.two_pow_dvd_ord
  exact (h4.trans h5).mul_left 2

end PI.HostPsiFactsWork
