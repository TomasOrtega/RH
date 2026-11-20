import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

/- English proof (translation)
Introduce `D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂`. Take `⟨lcV, scV, t2V⟩` from `GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V`. Take `⟨lcW, scW, t2W⟩` from `GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W`. Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Use `haveI : BorelSpace (GA D W) := ⟨rfl⟩`.

Use `haveI := hS.haarV`. Use `haveI := hS.haarW`. Take `⟨hfin, hK⟩` from `hKer ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ`. Take `⟨B₁, hB₁⟩` from `hK f₁ hf₁ φ₁ hφ₁ hc₁`. Take `⟨B₂, hB₂⟩` from `hK f₂ hf₂ φ₂ hφ₂ hc₂`.

Use `haveI : IsFiniteMeasure (νV.restrict 𝓗) := isFiniteMeasure_restrict.2 hfin`. Establish `hk : ∀ f, IsThetaFunO ψ V W f → Continuous fun p : GA D V × GA D W => thetaKO om p.1 p.2 f` using `fun f hf => hS.weil.om_cont f hf 0`. Use `set μG := νW.restrict 𝓖 with hμG`. Use `set μH := νV.restrict 𝓗 with hμH`. Use `set F : GA D V → GA D W × GA D W → ℂ := fun h p => thetaKO om h p.1 f₁ * star (φ₁ p.1) * (star (thetaKO om h p.2 f₂) * φ₂ p.2) with hF`.

Establish `hFc : Continuous (Function.uncurry F)`. Establish `a1 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.1 f₁` using `(hk f₁ hf₁).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))`. Establish `a2 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.2 f₂` using `(hk f₂ hf₂).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))`. Establish `b1 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₁ q.2.1` using `hφ₁.cont.comp (continuous_fst.comp continuous_snd)`. Establish `b2 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₂ q.2.2` using `hφ₂.cont.comp (continuous_snd.comp continuous_snd)`.

Conclude with `(a1.mul b1.star).mul (a2.star.mul b2)`. Establish `hFm : AEStronglyMeasurable (Function.uncurry F) (μH.prod (μG.prod μG))` using `hFc.aestronglyMeasurable`. Establish `hI1 : ∀ h, Integrable (fun g => thetaKO om h g f₁ * star (φ₁ g)) μG`. Introduce `h`. Use `((hB₁ h).1.norm).mono' (((hk f₁ hf₁).comp (continuous_const.prodMk continuous_id)).mul hφ₁.cont.star).aestronglyMeasurable (ae_of_all _ fun g => ?_)` and prove the remaining obligations.

Simplify using `[norm_mul]`. Establish `hI2 : ∀ h, Integrable (fun g => star (thetaKO om h g f₂) * φ₂ g) μG` using `fun h => (hB₂ h).1`. Establish `hFh : ∀ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h = ∫ p, F h p ∂(μG.prod μG)`. Introduce `h`. Rewrite using `[integral_prod_mul (fun g => thetaKO om h g f₁ * star (φ₁ g)) (fun g => star (thetaKO om h g f₂) * φ₂ g)]`.

Unfold `upLift`. Use `congr 1`. Rewrite using `[← hμG]`. Use `show (starRingEnd ℂ) _ = _`. Rewrite using `[← integral_conj]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `[Complex.star_def]`. Establish `hB₁0 : 0 ≤ B₁` using `le_trans (integral_nonneg fun g => by positivity) ((hB₁ 1).2)`. Establish `hB₂0 : 0 ≤ B₂` using `le_trans (integral_nonneg fun g => by positivity) ((hB₂ 1).2)`.

Establish `hnorm : ∀ h, ∫ p, ‖F h p‖ ∂(μG.prod μG) = (∫ g, ‖thetaKO om h g f₁‖ * ‖φ₁ g‖ ∂μG) * ∫ g, ‖thetaKO om h g f₂‖ * ‖φ₂ g‖ ∂μG`. Introduce `h`. Rewrite using `[← integral_prod_mul (fun g => ‖thetaKO om h g f₁‖ * ‖φ₁ g‖) (fun g => ‖thetaKO om h g f₂‖ * ‖φ₂ g‖)]`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Simplify using `[hF, norm_mul]`. Establish `hInt : Integrable (Function.uncurry F) (μH.prod (μG.prod μG))`. Rewrite using `[integrable_prod_iff hFm]`. Use `⟨ae_of_all _ fun h => (hI1 h).mul_prod (hI2 h), ?_⟩` and prove the remaining obligations. Use `(integrable_const (B₁ * B₂)).mono' hFm.norm.integral_prod_right' (ae_of_all _ fun h => ?_)` and prove the remaining obligations.

Simplify using `only [Function.uncurry_apply_pair]`. Rewrite using `[hnorm h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `mul_le_mul (hB₁ h).2 (hB₂ h).2 (integral_nonneg fun g => by positivity) hB₁0`. Establish `hsplit : ∀ (h : GA D V) (g : GA D W) (f : WO V W → ℂ), thetaKO om h g f = thetaKO om h 1 (om (1, g) f)`. Introduce `h g f`.

Unfold `thetaKO`. Rewrite using `[show ((h, g) : GA D V × GA D W) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply]`. Establish `hup : (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) = fun h => ∫ p, F h p ∂(μG.prod μG)` using `funext hFh`. Use `⟨fun h => (hB₁ h).1, ?_, ?_⟩` and prove the remaining obligations. Use `show Integrable _ μH`.

Rewrite using `[hup]`. Conclude with `hInt.integral_prod_left`. Establish `hpt : ∀ p : GA D W × GA D W, ∫ h, F h p ∂μH = ((νV 𝓗).toReal : ℂ) * (star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂))`. Introduce `p`. Establish `hsw` using `hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, p.1) f₁) (om (1, p.2) f₂) (hS.weil.om_pres _ _ hf₁) (hS.weil.om_pres _ _ hf₂)`.

Establish `he` using `hsw.tsum_eq`. Rewrite `he` using `[← hμH, tsum_mul_left]`. Establish `hfun : (fun h => F h p) = fun h => (star (φ₁ p.1) * φ₂ p.2) * (thetaKO om h 1 (om (1, p.1) f₁) * star (thetaKO om h 1 (om (1, p.2) f₂)))`. Use function extensionality and compare the values at `h`. Simplify using `only [hF]`.

Rewrite using `[hsplit h p.1 f₁, hsplit h p.2 f₂]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, integral_const_mul, ← he]`. Expand and normalize the polynomial expressions, which then agree. Use `show ∫ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂μH = _`.

Rewrite using `[hup, integral_integral_swap hInt, ← Measure.prod_restrict, ← hμG, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Rewrite using `[hpt p]`.
-/
theorem rallis_kernel_step : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨lcV, scV, t2V⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨lcW, scW, t2W⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := hS.haarV
  haveI := hS.haarW
  obtain ⟨hfin, hK⟩ := hKer ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  obtain ⟨B₁, hB₁⟩ := hK f₁ hf₁ φ₁ hφ₁ hc₁
  obtain ⟨B₂, hB₂⟩ := hK f₂ hf₂ φ₂ hφ₂ hc₂
  haveI : IsFiniteMeasure (νV.restrict 𝓗) := isFiniteMeasure_restrict.2 hfin
  have hk : ∀ f, IsThetaFunO ψ V W f → Continuous fun p : GA D V × GA D W => thetaKO om p.1 p.2 f :=
    fun f hf => hS.weil.om_cont f hf 0
  set μG := νW.restrict 𝓖 with hμG
  set μH := νV.restrict 𝓗 with hμH
  set F : GA D V → GA D W × GA D W → ℂ := fun h p =>
    thetaKO om h p.1 f₁ * star (φ₁ p.1) * (star (thetaKO om h p.2 f₂) * φ₂ p.2) with hF
  have hFc : Continuous (Function.uncurry F) := by
    have a1 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.1 f₁ :=
      (hk f₁ hf₁).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have a2 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.2 f₂ :=
      (hk f₂ hf₂).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    have b1 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₁ q.2.1 :=
      hφ₁.cont.comp (continuous_fst.comp continuous_snd)
    have b2 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₂ q.2.2 :=
      hφ₂.cont.comp (continuous_snd.comp continuous_snd)
    exact (a1.mul b1.star).mul (a2.star.mul b2)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μH.prod (μG.prod μG)) := hFc.aestronglyMeasurable
  have hI1 : ∀ h, Integrable (fun g => thetaKO om h g f₁ * star (φ₁ g)) μG := by
    intro h
    refine ((hB₁ h).1.norm).mono' (((hk f₁ hf₁).comp (continuous_const.prodMk continuous_id)).mul
      hφ₁.cont.star).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp [norm_mul]
  have hI2 : ∀ h, Integrable (fun g => star (thetaKO om h g f₂) * φ₂ g) μG := fun h => (hB₂ h).1
  have hFh : ∀ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h = ∫ p, F h p ∂(μG.prod μG) := by
    intro h
    rw [integral_prod_mul (fun g => thetaKO om h g f₁ * star (φ₁ g)) (fun g => star (thetaKO om h g f₂) * φ₂ g)]
    unfold upLift
    congr 1
    rw [← hμG]
    show (starRingEnd ℂ) _ = _
    rw [← integral_conj]
    congr 1
    funext g
    simp [Complex.star_def]
  have hB₁0 : 0 ≤ B₁ := le_trans (integral_nonneg fun g => by positivity) ((hB₁ 1).2)
  have hB₂0 : 0 ≤ B₂ := le_trans (integral_nonneg fun g => by positivity) ((hB₂ 1).2)
  have hnorm : ∀ h, ∫ p, ‖F h p‖ ∂(μG.prod μG) =
      (∫ g, ‖thetaKO om h g f₁‖ * ‖φ₁ g‖ ∂μG) * ∫ g, ‖thetaKO om h g f₂‖ * ‖φ₂ g‖ ∂μG := by
    intro h
    rw [← integral_prod_mul (fun g => ‖thetaKO om h g f₁‖ * ‖φ₁ g‖) (fun g => ‖thetaKO om h g f₂‖ * ‖φ₂ g‖)]
    congr 1
    funext p
    simp [hF, norm_mul]
  have hInt : Integrable (Function.uncurry F) (μH.prod (μG.prod μG)) := by
    rw [integrable_prod_iff hFm]
    refine ⟨ae_of_all _ fun h => (hI1 h).mul_prod (hI2 h), ?_⟩
    refine (integrable_const (B₁ * B₂)).mono' hFm.norm.integral_prod_right' (ae_of_all _ fun h => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hB₁ h).2 (hB₂ h).2 (integral_nonneg fun g => by positivity) hB₁0
  have hsplit : ∀ (h : GA D V) (g : GA D W) (f : WO V W → ℂ), thetaKO om h g f = thetaKO om h 1 (om (1, g) f) := by
    intro h g f
    unfold thetaKO
    rw [show ((h, g) : GA D V × GA D W) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply]
  have hup : (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) =
      fun h => ∫ p, F h p ∂(μG.prod μG) := funext hFh
  refine ⟨fun h => (hB₁ h).1, ?_, ?_⟩
  · show Integrable _ μH
    rw [hup]
    exact hInt.integral_prod_left
  · have hpt : ∀ p : GA D W × GA D W, ∫ h, F h p ∂μH = ((νV 𝓗).toReal : ℂ) * (star (φ₁ p.1) * φ₂ p.2 *
        ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
      intro p
      have hsw := hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, p.1) f₁) (om (1, p.2) f₂)
        (hS.weil.om_pres _ _ hf₁) (hS.weil.om_pres _ _ hf₂)
      have he := hsw.tsum_eq
      rw [← hμH, tsum_mul_left] at he
      have hfun : (fun h => F h p) = fun h => (star (φ₁ p.1) * φ₂ p.2) *
          (thetaKO om h 1 (om (1, p.1) f₁) * star (thetaKO om h 1 (om (1, p.2) f₂))) := by
        funext h
        simp only [hF]
        rw [hsplit h p.1 f₁, hsplit h p.2 f₂]
        ring
      rw [hfun, integral_const_mul, ← he]
      ring
    show ∫ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂μH = _
    rw [hup, integral_integral_swap hInt, ← Measure.prod_restrict, ← hμG, ← integral_const_mul]
    congr 1
    funext p
    rw [hpt p]

end GlobalTheory.RawLift

end
