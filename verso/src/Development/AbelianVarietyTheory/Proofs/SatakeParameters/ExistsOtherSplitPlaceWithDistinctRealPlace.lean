import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeSplitCm

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

namespace GlobalTheory.OtherSplitPlace

/- English proof (translation)
Introduce `E _ _ _ w₀`. Take `⟨p, hp, hmp, hs⟩` from `GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w`. Introduce `w hw`.

Establish `hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal` using `by show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Take `⟨a, b, hab, ha, hb⟩` from `GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv`. Distinguish the cases in `h : a = w`. Conclude with `⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩`.

Conclude with `⟨a, h, HeightOneSpectrum.ext ha⟩`. Use `haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hinj : Function.Injective (algebraMap ℤ (𝓞 E))` using `(algebraMap ℤ (𝓞 E)).injective_int`. Take `⟨Q, hQmax, hQ⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)`. Establish `hpQ : (p : 𝓞 E) ∈ Q`.

Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E))` using `hQ ▸ Ideal.subset_span rfl`. Simplify using `using this`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Set `w₁ : HeightOneSpectrum (𝓞 E)` to `⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩`. Use `⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩` and prove the remaining obligations.

Establish `hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal`. Establish `hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal` using `by show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hpQ`. Rewrite `hv` using `[heq]`.

Establish `: algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal` using `hv`. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal` using `Ideal.absNorm_mem _`. Establish `hN0 : 0 < Ideal.absNorm w₀.asIdeal` using `Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))`. Establish `hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal)` using `(Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))`.

Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))`. Apply `w₀.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Simplify using `using hp₀`.

Simplify using `using hN`.
-/
theorem exists_isSplitAt_under_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧
      w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  intro E _ _ _ w₀
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := hQ ▸ Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩

  have hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w₀.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w₀.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hp₀
  · simpa using hN

end GlobalTheory.OtherSplitPlace
