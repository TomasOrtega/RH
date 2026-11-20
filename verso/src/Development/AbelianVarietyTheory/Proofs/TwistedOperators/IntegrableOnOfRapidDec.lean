import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size

namespace GlobalTheory.Chain.LiftConv

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

/- English proof (translation)
Introduce `γ hγ h`. Establish `hsplit : ((g, γ * h) : GA D V × GA D W) = (1, γ) * (g, h)`. Apply the tactic sequence `ext <;> simp`. Establish `hpres : IsThetaFunO ψ V W (ω (g, h) f)` using `hω.om_pres _ _ hf`. Unfold `thetaKO`.

Rewrite using `[hsplit, map_mul, Module.End.mul_apply]`. Conclude with `hω.om_aut 1 (one_mem _) γ hγ _ hpres`.
-/
theorem thetaKO_left (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f = thetaKO ω g h f := by
  intro γ hγ h

  have hsplit : ((g, γ * h) : GA D V × GA D W) = (1, γ) * (g, h) := by
    ext <;> simp
  have hpres : IsThetaFunO ψ V W (ω (g, h) f) := hω.om_pres _ _ hf
  unfold thetaKO
  rw [hsplit, map_mul, Module.End.mul_apply]
  exact hω.om_aut 1 (one_mem _) γ hγ _ hpres

/- English proof (translation)
Establish `hpair : Continuous fun h : GA D W => ((g, h) : GA D V × GA D W)` using `by fun_prop`. Unfold `thetaKO`. Conclude with `(hω.om_cont f hf 0).comp hpair`.
-/
theorem thetaKO_continuous (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    Continuous fun h => thetaKO ω g h f := by

  have hpair : Continuous fun h : GA D W => ((g, h) : GA D V × GA D W) := by fun_prop
  unfold thetaKO
  exact (hω.om_cont f hf 0).comp hpair

/- English proof (translation)
Take `⟨A, d, hAd⟩` from `hG V.rank W.rank`. Take `⟨U, hUo, hfU⟩` from `GlobalTheory.Size.isTheta_iff_level.mp hf`. Take `⟨μ, 𝓕, hcov⟩` from `GlobalTheory.Size.exists_isCovolOne V W`. Take `⟨C, -, hC⟩` from `(hAd V W rfl rfl).real ψ hθ hUo`. Take `⟨-, hbd⟩` from `hC χS χT ω hω μ 𝓕 hcov f hfU`.

Use `⟨C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A, A, fun h => ?_⟩` and prove the remaining obligations. Establish `key` using `hbd g h`. Unfold `thetaKO`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaKO_modGrowth (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (g : GA D V) : ModGrowth W fun h => thetaKO ω g h f := by
  obtain ⟨A, d, hAd⟩ := hG V.rank W.rank
  obtain ⟨U, hUo, hfU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hf
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (hAd V W rfl rfl).real ψ hθ hUo
  obtain ⟨-, hbd⟩ := hC χS χT ω hω μ 𝓕 hcov f hfU

  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A, A, fun h => ?_⟩
  have key := hbd g h
  unfold thetaKO
  calc ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := key
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A * height W h ^ A := by
      rw [mul_pow]; ring

/- English proof (translation)
Establish `hcont` using `thetaKO_continuous hω hf g`. Conclude with `hF.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth hG hθ hω hf g) (thetaKO_left hω hf g) hcont.aestronglyMeasurable`.
-/
theorem integrableOn_of_rapidDec (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) {F : GA D W → ℂ} (hF : RapidDec W F) (g : GA D V) :
    IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν := by
  have hcont := thetaKO_continuous hω hf g
  exact hF.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth hG hθ hω hf g)
    (thetaKO_left hω hf g) hcont.aestronglyMeasurable

/- English proof (translation)
Introduce `V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 f F hf hFs hFc g`. Establish `hdec : RapidDec W F` using `rapidDec_of_cuspForm hP hθ hFs hFc`. Conclude with `integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hdec g`.
-/
theorem liftInteg_of_growth (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) :
    LiftInteg D := by
  intro V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 f F hf hFs hFc g

  have hdec : RapidDec W F := rapidDec_of_cuspForm hP hθ hFs hFc
  exact integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hdec g

end GlobalTheory.Chain.LiftConv
