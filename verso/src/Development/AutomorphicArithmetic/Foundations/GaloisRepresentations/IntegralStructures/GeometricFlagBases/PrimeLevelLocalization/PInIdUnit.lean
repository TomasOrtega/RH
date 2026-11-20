import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.StGood

noncomputable section

open NumberField IsDedekindDomain
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Express the relevant statement in the definitionally equal form `Valued.v ((algebraMap (𝓞 E) E s : E) : HeightOneSpectrum.adicCompletion E w) = 1`. Rewrite using `[HeightOneSpectrum.adicCompletion.valued_coe, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `hs`.
-/
private theorem isUnit_algebraMap_adicCompletionIntegers_of_not_mem (E : Type) [Field E] [NumberField E] (w : Plc E) (s : 𝓞 E)
    (hs : s ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w) s) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v ((algebraMap (𝓞 E) E s : E) : HeightOneSpectrum.adicCompletion E w) = 1
  rw [HeightOneSpectrum.adicCompletion.valued_coe, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  exact hs

/- English proof (translation)
Introduce `E _ _ w b c hc y`. Take `⟨s, hsc, hsw⟩` from `hc`. Establish `htop : Ideal.map (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w)) c = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsc) (isUnit_algebraMap_adicCompletionIntegers_of_not_mem E w s hsw)`. Unfold `InId`. Rewrite using `[Ideal.map_mul, htop, Ideal.mul_top]`.
-/
theorem inIdUnit_holds : InIdUnit := by
  intro E _ _ w b c hc y
  obtain ⟨s, hsc, hsw⟩ := hc
  have htop : Ideal.map (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w)) c = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsc) (isUnit_algebraMap_adicCompletionIntegers_of_not_mem E w s hsw)
  unfold InId
  rw [Ideal.map_mul, htop, Ideal.mul_top]

end UpperTheory.Gal.Int.Geo.Pl

end
