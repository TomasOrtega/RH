import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

/- English proof (translation)
Simplify using `only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]`.
-/
theorem mem_incIdeal_iffR {P : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ u ∈ incidence P k, aeval u g = 0 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

/- English proof (translation)
Take `⟨x, hx0, hxW, hxu⟩` from `hu`. Conclude with `⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩`.
-/
theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

/- English proof (translation)
Take `⟨x, hx0, hxJ, hxu⟩` from `hu`. Set `φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F` to `aeval x`. Establish `hP : (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime _`. Establish `hJP : J ≤ RingHom.ker φ` using `fun g hg => RingHom.mem_ker.mpr (hxJ g hg)`. Take `⟨W, hW, hWP⟩` from `Ideal.exists_minimalPrimes_le hJP`.

Use `⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hrel`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `hj : X j ∈ W`.

Assume the negation of the conclusion as `hj`. Conclude with `hrel ⟨j, hj⟩`. Use `RingHom.mem_ker.mp (hWP hj)` as an intermediate fact. Simplify `this` using `[φ]`.
-/
theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

/- English proof (translation)
Rewrite using `[Finsupp.mem_support_iff]`. Unfold `fundCycle`. Rewrite using `[Finsupp.onFinset_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `h'`. Conclude with `h (if_neg h')`. Introduce `h`. Rewrite using `[if_pos h, localMult_eq_one_of_isRadical hJ h.1]`. Conclude with `one_ne_zero`.
-/
theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

/- English proof (translation)
Introduce `F _ n k J h hJh hJr hch`. Establish `hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W` using `fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW`. Establish `hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J` using `fun W hW => (mem_support_fundCycle_iff hJr).mp hW`. Establish `hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k`. Introduce `g`.

Rewrite using `[← hch.2 g]`. Prove the components needed by the constructor for the conclusion. Introduce `hg W hW`. Conclude with `mem_incIdeal_iffR.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)`. Introduce `hg u hu`.

Take `⟨W, hW, huW⟩` from `exists_relComps_of_mem_incidence hu`. Conclude with `mem_incIdeal_iffR.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW`. Establish `hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support, incIdeal W' k ≤ incIdeal W k → W' = W`. Introduce `W hW W' hW' hle`. Establish `hne : incIdeal W' k ≠ ⊥` using `fun hb => hch.1 (by`.

Use `(hspan h).mp dvd_rfl W' hW'` as an intermediate fact. Rewrite using `[hb, Ideal.mem_bot] at this)` and apply the resulting hypothesis. Establish `hWW' : W' ≤ W` using `hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle`. Conclude with `le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')`. Establish `hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q}`.

Introduce `W hW`. Establish `hPW : (incIdeal W k).IsPrime` using `hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant`. Establish `hhW : h ∈ incIdeal W k` using `(hspan h).mp dvd_rfl W hW`. Take `⟨u, hu⟩` from `UniqueFactorizationMonoid.factors_prod hch.1`. Establish `hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k`.

Rewrite `hhW` using `[← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit]`. Then use the resulting hypothesis. Take `⟨q, hqf, hqW⟩` from `(hPW.multiset_prod_mem_iff_exists_mem _).1 hprod`. Establish `hq : Prime q` using `UniqueFactorizationMonoid.prime_of_factor q hqf`. Establish `hqh : q ∣ h` using `UniqueFactorizationMonoid.dvd_of_mem_factors hqf`. Establish `hqle : Ideal.span {q} ≤ incIdeal W k` using `(Ideal.span_singleton_le_iff_mem _).mpr hqW`.

Use `⟨q, hq, le_antisymm ?_ hqle⟩` and prove the remaining obligations. Establish `hqP : (Ideal.span {q}).IsPrime` using `(Ideal.span_singleton_prime hq.ne_zero).mpr hq`. Establish `hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q}`. Introduce `g hg`. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `dvd_trans hqh ((hspan g).mpr fun W' hW' => Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)`. Take `⟨W', hW', hle⟩` from `hqP.inf_le'.mp hinf`. Establish `hW'W : W' = W` using `hsep W hW W' hW' (hle.trans hqle)`. Rewrite using `[← hW'W]`. Conclude with `hle`.

Use `choose! q hq hqspan using hprin`. Establish `hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h`. Use `Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_` and prove the remaining obligations. Introduce `W hW W' hW' hne`. Use `(hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_` and prove the remaining obligations.

Establish `hmem : q W' ∈ incIdeal W k`. Rewrite using `[hqspan W hW]`. Conclude with `Ideal.mem_span_singleton.mpr hdvd`. Use `(hsep W hW W' hW' ?_).symm` and prove the remaining obligations. Rewrite using `[hqspan W' hW']`.

Conclude with `(Ideal.span_singleton_le_iff_mem _).mpr hmem`. Use `(hspan h).mp dvd_rfl W hW` as an intermediate fact. Rewrite `this` using `[hqspan W hW]`. Conclude with `Ideal.mem_span_singleton.mp this`. Establish `hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W`.

Use `(hspan _).mpr fun W hW => ?_` and prove the remaining obligations. Rewrite using `[hqspan W hW]`. Conclude with `Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)`. Take `⟨u, hu⟩` from `associated_of_dvd_dvd hdvd₁ hdvd₂`. Take `⟨r, hr, hur⟩` from `(isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp u.isUnit`.

Use `⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_incIdeal_iffR, hqspan W hW, Ideal.mem_span_singleton]`. Rewrite using `[Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one], ← hu, hur, mul_comm]`.
-/
theorem ChowFormReduced.proof (hPrime : IncIdealPrime.Statement) (hSep : IncIdealSeparate.Statement) :
    ChowFormReduced.Statement := by
  classical
  intro F _ n k J h hJh hJr hch
  have hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W :=
    fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW
  have hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J :=
    fun W hW => (mem_support_fundCycle_iff hJr).mp hW

  have hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k := by
    intro g
    rw [← hch.2 g]
    constructor
    · intro hg W hW
      exact mem_incIdeal_iffR.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)
    · intro hg u hu
      obtain ⟨W, hW, huW⟩ := exists_relComps_of_mem_incidence hu
      exact mem_incIdeal_iffR.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW

  have hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support,
      incIdeal W' k ≤ incIdeal W k → W' = W := by
    intro W hW W' hW' hle
    have hne : incIdeal W' k ≠ ⊥ := fun hb => hch.1 (by
      have := (hspan h).mp dvd_rfl W' hW'
      rwa [hb, Ideal.mem_bot] at this)
    have hWW' : W' ≤ W := hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle
    exact le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')

  have hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q} := by
    intro W hW
    have hPW : (incIdeal W k).IsPrime := hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant
    have hhW : h ∈ incIdeal W k := (hspan h).mp dvd_rfl W hW
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hch.1
    have hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k := by
      rwa [← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit] at hhW
    obtain ⟨q, hqf, hqW⟩ := (hPW.multiset_prod_mem_iff_exists_mem _).1 hprod
    have hq : Prime q := UniqueFactorizationMonoid.prime_of_factor q hqf
    have hqh : q ∣ h := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
    have hqle : Ideal.span {q} ≤ incIdeal W k := (Ideal.span_singleton_le_iff_mem _).mpr hqW
    refine ⟨q, hq, le_antisymm ?_ hqle⟩
    have hqP : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q} := by
      intro g hg
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hqh ((hspan g).mpr fun W' hW' =>
        Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)
    obtain ⟨W', hW', hle⟩ := hqP.inf_le'.mp hinf
    have hW'W : W' = W := hsep W hW W' hW' (hle.trans hqle)
    rw [← hW'W]
    exact hle
  choose! q hq hqspan using hprin

  have hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h := by
    refine Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_
    · intro W hW W' hW' hne
      refine (hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_
      have hmem : q W' ∈ incIdeal W k := by
        rw [hqspan W hW]
        exact Ideal.mem_span_singleton.mpr hdvd
      refine (hsep W hW W' hW' ?_).symm
      rw [hqspan W' hW']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    · have := (hspan h).mp dvd_rfl W hW
      rw [hqspan W hW] at this
      exact Ideal.mem_span_singleton.mp this
  have hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W := by
    refine (hspan _).mpr fun W hW => ?_
    rw [hqspan W hW]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁ hdvd₂
  obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp
    u.isUnit
  refine ⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩
  · rw [← mem_incIdeal_iffR, hqspan W hW, Ideal.mem_span_singleton]
  · rw [Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one],
      ← hu, hur, mul_comm]

end

end GroundTheory.Heights₂.Heights
