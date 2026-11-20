import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent

noncomputable section

namespace GlobalTheory.TwU.Served

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical NumberField

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem hP_ne_zero (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) (hn : HNeZero D.host p) : hP D p ≠ 0 := by
  obtain ⟨P, hP', hL, σ, hσ⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.exists_frob D.host p hp hc
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP', hL, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have h3 := @HNeZero.ne_one _ _ _ hn P₂ h1 h2 σ₂ hσ₂
  intro h0
  apply h3
  rw [he]
  have h4 := Formalism.HC.Frame.iota_iotaInv D.R.toFrame (Classical.epsilon (fun g => g ∈ frobSet D p)).2
  unfold hP at h0
  rw [h0, Formalism.HC.Frame.iota_zero] at h4
  exact h4.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

A detailed English derivation is pending.
-/
theorem jacobi_eq_neg_one (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  obtain ⟨h2, hq, hd, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : (-(D.host.d : ℤ)).gcd (p : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes D.host.hyp.2.1 hp).2 (Ne.symm hd)
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h | h | h
  · exact absurd hcop (jacobiSym.eq_zero_iff_not_coprime.1 h)
  · exact absurd h hjd
  · exact h

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem coprime_absNorm_ccK (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  obtain ⟨-, -, -, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  obtain ⟨P, hpP, hdvd⟩ := GlobalTheory.HalfCompare.exists_place_of_dvd_absNorm hp D.host.ccK h
  obtain ⟨hNP, hj⟩ := D.host.ccK_split P.asIdeal P.isPrime (Ideal.le_of_dvd hdvd)
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 ((hlP p).1 hpP)
  have hlN : l = Ideal.absNorm P.asIdeal :=
    (Nat.prime_dvd_prime_iff_eq hl hNP).1 ((hlP _).1 (Ideal.absNorm_mem P.asIdeal))
  rw [← hlN, hlp] at hj
  exact hjd hj

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem served_facts : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p →
    hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p :=
  fun D p hp hc hn => ⟨hP_ne_zero D p hp hc hn, jacobi_eq_neg_one D p hp hc, coprime_absNorm_ccK D p hp hc⟩

end GlobalTheory.TwU.Served
