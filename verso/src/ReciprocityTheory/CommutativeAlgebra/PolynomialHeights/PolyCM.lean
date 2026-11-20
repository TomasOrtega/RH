import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolySeq
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.RingKrullDimLocalizationQuotientEqHeight

namespace ReciprocityTheory.CA

open IsLocalRing

/- English proof (translation)
Take `⟨hnoeth, n, hdim, rs, hlen, hmem, hreg⟩` from `hP`. Use `haveI := hnoeth`. Take `⟨ss, hsslen, hssmem, hssreg⟩` from `exists_isWeaklyRegular_mvPolynomial hmem hreg.toIsWeaklyRegular N 𝔑 h`. Establish `hle : ((rs.length + N : ℕ) : ℕ∞) ≤ 𝔑.height`. Rewrite using `[← hsslen]`.

Conclude with `length_le_height_of_isWeaklyRegular 𝔑 hssmem hssreg`. Establish `hge : (𝔑.height : WithBot ℕ∞) ≤ ringKrullDim P + N`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]`. Establish `hht : (𝔑.height : WithBot ℕ∞) = ((n + N : ℕ) : WithBot ℕ∞)`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite `hge` using `[hdim]`. Conclude with `hge` after adjusting the coercions. Rewrite `hle` using `[hlen]`. Conclude with `hle` after adjusting the coercions.

Use `⟨⟨?_, n + N, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `IsLocalization.isNoetherianRing 𝔑.primeCompl _ inferInstance`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height 𝔑, hht]`. Use `depthGE_localization_of_isWeaklyRegular 𝔑 hssmem hssreg` as an intermediate fact. Rewrite `this` using `[hsslen, hlen]`. Then use the resulting hypothesis.

Rewrite using `[hht, hdim]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem isCM_localization_mvPolynomial {P : Type*} [CommRing P] [IsLocalRing P] (hP : IsCM P) (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) P)) [𝔑.IsMaximal]
    (h : 𝔑.comap MvPolynomial.C = maximalIdeal P) :
    IsCM (Localization.AtPrime 𝔑) ∧ (𝔑.height : WithBot ℕ∞) = ringKrullDim P + N := by
  obtain ⟨hnoeth, n, hdim, rs, hlen, hmem, hreg⟩ := hP
  haveI := hnoeth
  obtain ⟨ss, hsslen, hssmem, hssreg⟩ :=
    exists_isWeaklyRegular_mvPolynomial hmem hreg.toIsWeaklyRegular N 𝔑 h
  have hle : ((rs.length + N : ℕ) : ℕ∞) ≤ 𝔑.height := by
    rw [← hsslen]; exact length_le_height_of_isWeaklyRegular 𝔑 hssmem hssreg
  have hge : (𝔑.height : WithBot ℕ∞) ≤ ringKrullDim P + N := by
    calc (𝔑.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin N) P) :=
          Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsMaximal.ne_top ‹_›)
      _ = ringKrullDim P + N := by
          rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card,
            Fintype.card_fin]
  have hht : (𝔑.height : WithBot ℕ∞) = ((n + N : ℕ) : WithBot ℕ∞) := by
    apply le_antisymm
    · rw [hdim] at hge
      exact_mod_cast hge
    · rw [hlen] at hle
      exact_mod_cast hle
  refine ⟨⟨?_, n + N, ?_, ?_⟩, ?_⟩
  · exact IsLocalization.isNoetherianRing 𝔑.primeCompl _ inferInstance
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔑, hht]
  · have := depthGE_localization_of_isWeaklyRegular 𝔑 hssmem hssreg
    rwa [hsslen, hlen] at this
  · rw [hht, hdim]
    push_cast
    rfl

/- English proof (translation)
Establish `hdisj : Disjoint (𝔑.primeCompl : Set S) 𝔔`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hxQ`. Conclude with `hx (hle hxQ)`. Use `haveI : (𝔔.map (algebraMap S (Localization.AtPrime 𝔑))).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔔 ‹_› hdisj`.

Establish `h1` using `h.height_add_ringKrullDim_quotient (𝔔.map (algebraMap S (Localization.AtPrime 𝔑)))`. Rewrite `h1` using `[IsLocalization.height_map_of_disjoint 𝔑.primeCompl 𝔔 hdisj, ringKrullDim_localization_quotient_eq_height 𝔔 𝔑 hle, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔑]`. Conclude with `h1.symm` after adjusting the coercions.
-/
theorem height_eq_add_of_isCM_localization {S : Type*} [CommRing S] (𝔑 𝔔 : Ideal S) [𝔑.IsPrime]
    [𝔔.IsPrime] (h : IsCM (Localization.AtPrime 𝔑)) (hle : 𝔔 ≤ 𝔑) :
    𝔑.height = 𝔔.height + (𝔑.map (Ideal.Quotient.mk 𝔔)).height := by
  have hdisj : Disjoint (𝔑.primeCompl : Set S) 𝔔 := by
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hx (hle hxQ)
  haveI : (𝔔.map (algebraMap S (Localization.AtPrime 𝔑))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔔 ‹_› hdisj
  have h1 := h.height_add_ringKrullDim_quotient (𝔔.map (algebraMap S (Localization.AtPrime 𝔑)))
  rw [IsLocalization.height_map_of_disjoint 𝔑.primeCompl 𝔔 hdisj,
    ringKrullDim_localization_quotient_eq_height 𝔔 𝔑 hle,
    IsLocalization.AtPrime.ringKrullDim_eq_height 𝔑] at h1
  exact_mod_cast h1.symm

end ReciprocityTheory.CA
