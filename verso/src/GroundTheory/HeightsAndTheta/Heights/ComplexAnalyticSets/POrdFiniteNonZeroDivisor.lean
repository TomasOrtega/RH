import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

variable {n : ℕ}

/- English proof (translation)
The claim follows from `IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective`.
-/
theorem isLocalRing_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective

/- English proof (translation)
Introduce `n I q f hrad hdim hord`. Establish `: Nontrivial (curveLocalRing I q)`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Rewrite `hdim` using `[ringKrullDim_eq_bot_of_subsingleton]`.

Conclude with `WithBot.bot_ne_coe hdim`. Establish `: IsLocalRing (curveLocalRing I q)` using `isLocalRing_curveLocalRing I q`. Establish `: IsReduced (curveLocalRing I q)` using `isReduced_curveLocalRing I q hrad`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `y hyx`.

Assume the negation of the conclusion as `hy`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by`. Establish `: y ∉ (⊥ : Ideal (curveLocalRing I q)).radical`. Introduce and unpack `⟨k, hk⟩`. Conclude with `hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)`.

Simplify `this` using `[← Ideal.sInf_minimalPrimes, minimalPrimes]`. Establish `hpP : p.IsPrime` using `hp.1.1`. Establish `hxp` using `(hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp`. Establish `hpmax : ¬ p.IsMaximal`. Introduce `hm`.

Establish `h1` using `IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)`. Rewrite `h1` using `[← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim]`. Conclude with `absurd h1 (by decide)`. Establish `: Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q)` using `inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q) (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))`. Take `⟨Q, -, hQ, hQp⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q)) (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap_curveNormalisation_injective I q)]; exact bot_le)`.

Take `⟨P, hPm, hQP⟩` from `Ideal.exists_le_maximal Q hQ.ne_top`. Apply `hord ⟨P, hPm⟩` to reduce the goal to its premises. Establish `: P.IsPrime` using `hPm.isPrime`. Establish `hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q` using `Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)`. Use `set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def`.

Establish `: Q'.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd`. Establish `hQ'u : Q'.under _ = Q` using `IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd`. Establish `hle : Ideal.span {algebraMap (curveNormalisation I q) (Localization.AtPrime P) (algebraMap (curveLocalRing I q) (curveNormalisation I q) (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))} ≤ Q'`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations.

Rewrite `hxp` using `[← hQp]`. Conclude with `hxp`. Express the relevant statement in the definitionally equal form `Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]`.

Take `⟨-, hart⟩` from `hne`. Establish `: IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q')` using `isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)`. Establish `: IsArtinianRing (Localization.AtPrime P ⧸ Q')` using `isArtinian_of_tower (Localization.AtPrime P) this`. Establish `hQ'max : Q'.IsMaximal` using `Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)`. Establish `hQeq : Q = P`.

Rewrite using `[← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]`. Apply `hpmax` to reduce the goal to its premises. Rewrite using `[← hQp]`. Establish `: Q.IsMaximal` using `hQeq ▸ hPm`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q`.
-/
theorem OrdFiniteNonZeroDivisor.proof : OrdFiniteNonZeroDivisor.Statement := by
  intro n I q f hrad hdim hord
  have : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing (curveLocalRing I q) := isLocalRing_curveLocalRing I q
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  rw [mem_nonZeroDivisors_iff_right]
  intro y hyx
  by_contra hy

  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by
    have : y ∉ (⊥ : Ideal (curveLocalRing I q)).radical := by
      rintro ⟨k, hk⟩
      exact hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
    simpa [← Ideal.sInf_minimalPrimes, minimalPrimes] using this
  have hpP : p.IsPrime := hp.1.1
  have hxp := (hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp

  have hpmax : ¬ p.IsMaximal := by
    intro hm
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)
    rw [← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim] at h1
    exact absurd h1 (by decide)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q))
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (algebraMap_curveNormalisation_injective I q)]; exact bot_le)
  obtain ⟨P, hPm, hQP⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  apply hord ⟨P, hPm⟩
  have : P.IsPrime := hPm.isPrime
  have hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q :=
    Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)
  set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd
  have hQ'u : Q'.under _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd
  have hle : Ideal.span {algebraMap (curveNormalisation I q) (Localization.AtPrime P)
      (algebraMap (curveLocalRing I q) (curveNormalisation I q)
        (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))} ≤ Q' := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hQp] at hxp
    exact hxp

  change Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  have : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q') :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : IsArtinianRing (Localization.AtPrime P ⧸ Q') := isArtinian_of_tower (Localization.AtPrime P) this
  have hQ'max : Q'.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hQeq : Q = P := by
    rw [← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]
  apply hpmax
  rw [← hQp]
  have : Q.IsMaximal := hQeq ▸ hPm
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q

end GroundTheory.Heights₂.Heights
