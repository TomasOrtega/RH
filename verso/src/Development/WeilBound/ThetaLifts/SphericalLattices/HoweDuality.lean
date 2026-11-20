import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.ThetaLifts.SphericalLattices.UnrAtDiv
import Development.WeilBound.ThetaLifts.SphericalLattices.LocDataV
import Development.WeilBound.ThetaLifts.SphericalLattices.LocDataVAlt
import Development.WeilBound.ThetaLifts.SphericalLattices.GenOf

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v he`. Take `⟨⟨w, hin⟩, hvT⟩` from `inert_ctx hT he`. Establish `ha : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.α u` using `fun u hu => hT.chars.unrα u fun h => hvT (hu ▸ h)`. Establish `hb : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.β u` using `fun u hu => hT.chars.unrβ u fun h => hvT (hu ▸ h)`. Use `⟨fun ω ρ hL => ?_, fun ω ρ hL => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `fix_of hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hb (fun u hu => unrAt_div (hb u hu) (ha u hu)) hL`. Take `⟨h3, h4⟩` from `gen_of hL (locDataV hT hin hvT)`. Conclude with `⟨h1, h2, h3, h4⟩`. Take `⟨h1, h2⟩` from `fix_of hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' ha (fun u hu => unrAt_div (ha u hu) (hb u hu)) hL`. Take `⟨h3, h4⟩` from `gen_of hL (locDataV' hT hin hvT)`.

Conclude with `⟨h1, h2, h3, h4⟩`.
-/
theorem howeInert : HoweInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨⟨w, hin⟩, hvT⟩ := inert_ctx hT he
  have ha : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.α u :=
    fun u hu => hT.chars.unrα u fun h => hvT (hu ▸ h)
  have hb : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.β u :=
    fun u hu => hT.chars.unrβ u fun h => hvT (hu ▸ h)
  refine ⟨fun ω ρ hL => ?_, fun ω ρ hL => ?_⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hb
      (fun u hu => unrAt_div (hb u hu) (ha u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' ha
      (fun u hu => unrAt_div (ha u hu) (hb u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV' hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩

end PositivityTheory.Sph

end
