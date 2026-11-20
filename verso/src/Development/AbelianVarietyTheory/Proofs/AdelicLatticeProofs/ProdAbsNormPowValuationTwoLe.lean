import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Introduce `F _ _ S e h`. Establish `hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)}`. Introduce `v hv`. Rewrite using `[← HeightOneSpectrum.intValuation_le_pow_iff_dvd]`. Establish `h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2` using `HeightOneSpectrum.valuation_of_algebraMap v 2`.

Rewrite `h2` using `[map_ofNat, h v hv]`. Conclude with `h2.ge`. Establish `hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)}`. Use `Finset.prod_dvd_of_coprime ?_ hdvd` and prove the remaining obligations. Introduce `v _ w _ hvw`.

Use `IsCoprime.pow ?_` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal (fun hh => hvw (HeightOneSpectrum.ext hh))`. Establish `hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F`. Rewrite using `[Ideal.absNorm_span_singleton]`.

Establish `: (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Simplify using `[Int.natAbs_pow]`. Establish `h3` using `map_dvd Ideal.absNorm hprod`. Rewrite `h3` using `[hn, map_prod]`.

Simplify using `only [map_pow] at h3`. Conclude with `Nat.le_of_dvd (by positivity) h3`.
-/
theorem prod_absNorm_pow_le_two_pow :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  intro F _ _ S e h
  have hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    intro v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    have h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2 :=
      HeightOneSpectrum.valuation_of_algebraMap v 2
    rw [map_ofNat, h v hv] at h2
    exact h2.ge
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro v _ w _ hvw
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun hh => hvw (HeightOneSpectrum.ext hh))
  have hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hn, map_prod] at h3
  simp only [map_pow] at h3
  exact Nat.le_of_dvd (by positivity) h3

end GlobalTheory.QNorm
