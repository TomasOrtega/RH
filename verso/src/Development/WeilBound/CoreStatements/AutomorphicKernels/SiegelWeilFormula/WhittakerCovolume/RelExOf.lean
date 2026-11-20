import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SdEx
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Assemble

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

/- English proof (translation)
Introduce `_ _ F E _ _ _ _ _ σ d R Φ _ P gf hP x t u hx T hTnd`. Take `⟨η, hOf, hη, hherm, hof, haniso, hcm, hJ, hTT⟩` from `hA F E σ d`. Take `⟨T₀, hrat, hTdh, hTdd⟩` from `hTT T hTnd`. Take `⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩` from `hR F E σ d R Φ P gf hP x t u hx η hη hherm`. Take `⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩` from `hS F E σ hcm d.m (Jd d η) hJ d.B.ψ hchr d.n`.

Conclude with `⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, ⟨hx, hrat, hη, hherm, hof, hth, hfr, hg⟩, hΦg, haniso, hεs, hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hpf, hpr, hμ, hν⟩`.
-/
theorem relEx_of (hA : RelAlg) (hS : SdEx) (hR : ThetaDictR.RelRealP) : RelEx := by
  intro _ _ F E _ _ _ _ _ σ d R Φ _ P gf hP x t u hx T hTnd
  obtain ⟨η, hOf, hη, hherm, hof, haniso, hcm, hJ, hTT⟩ := hA F E σ d
  obtain ⟨T₀, hrat, hTdh, hTdd⟩ := hTT T hTnd
  obtain ⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩ :=
    hR F E σ d R Φ P gf hP x t u hx η hη hherm
  obtain ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ := hS F E σ hcm d.m (Jd d η) hJ d.B.ψ hchr d.n
  exact ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, ⟨hx, hrat, hη, hherm, hof, hth, hfr, hg⟩, hΦg, haniso, hεs,
    hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hpf, hpr, hμ, hν⟩

/- English proof (translation)
The claim follows from `relEx_of relAlg_pf sdEx ThetaDictR.relReal`.
-/
theorem relEx : RelEx := relEx_of relAlg_pf sdEx ThetaDictR.relReal

end PositivityTheory.SiegelWeilFormula.KWhit

end
