import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceInverseGramConjSmulEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

/- English proof (translation)
Use `show f (reW S T b (ratW T (reS S b) γ + w)) = ψ (-(symplOH (reS S b) T (ratW T (reS S b) γ) w)) * f (reW S T b w)`. Rewrite using `[reW_add, ← symplOH_reW, reW_ratW S T b γ]`. Conclude with `hf.quasi _ _`. Use `level := by`. Take `⟨U, hU, hfU⟩` from `hf.level`.

Use `⟨U.comap (reWAdd S T b), hU.preimage (reW_continuous S T b), fun u hu hu0 => ?_⟩` and prove the remaining obligations. Rewrite using `[heisO_reF]`. Conclude with `congrArg (reF S T b) (hfU _ hu ((reW_map_eq_zero S T b _ u).2 hu0))`. Use `cont := hf.cont.comp (reW_continuous S T b)`. Use `smooth k L hL hL0 w := by`.

Use `hf.smooth k ((reWAdd S T b).comp L) ((reW_continuous S T b).comp hL) (fun t => (reW_map_eq_zero S T b _ (L t)).2 (hL0 t)) (reW S T b w)` as an intermediate fact. Establish `e : (fun t => reF S T b f (w + L t)) = fun t => f (reW S T b w + (reWAdd S T b).comp L t)`. Use function extensionality and compare the values at `fun t => by rw [reF_apply, reW_add]; rfl`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem isThetaFunO_reF (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ (reS S b) T (reF S T b f) where
  quasi γ w := by
    show f (reW S T b (ratW T (reS S b) γ + w)) = ψ (-(symplOH (reS S b) T (ratW T (reS S b) γ) w)) * f (reW S T b w)
    rw [reW_add, ← symplOH_reW, reW_ratW S T b γ]
    exact hf.quasi _ _
  level := by
    obtain ⟨U, hU, hfU⟩ := hf.level
    refine ⟨U.comap (reWAdd S T b), hU.preimage (reW_continuous S T b), fun u hu hu0 => ?_⟩
    rw [heisO_reF]
    exact congrArg (reF S T b) (hfU _ hu ((reW_map_eq_zero S T b _ u).2 hu0))
  cont := hf.cont.comp (reW_continuous S T b)
  smooth k L hL hL0 w := by
    have := hf.smooth k ((reWAdd S T b).comp L) ((reW_continuous S T b).comp hL)
      (fun t => (reW_map_eq_zero S T b _ (L t)).2 (hL0 t)) (reW S T b w)
    have e : (fun t => reF S T b f (w + L t)) = fun t => f (reW S T b w + (reWAdd S T b).comp L t) :=
      funext fun t => by rw [reF_apply, reW_add]; rfl
    rw [e]; exact this

/- English proof (translation)
Establish `h` using `isThetaFunO_reF (reS S b) T S.frame ψ _ hf`. Establish `e : reF (reS S b) T S.frame (reF S T b f) = f`. Use function extensionality and compare the values at `x`. Conclude with `congrArg f (reW_reWinv S T b x)`. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem isThetaFunO_of_reF (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ (reS S b) T (reF S T b f)) : IsThetaFunO ψ S T f := by
  have h := isThetaFunO_reF (reS S b) T S.frame ψ _ hf
  have e : reF (reS S b) T S.frame (reF S T b f) = f := by
    funext x
    exact congrArg f (reW_reWinv S T b x)
  rw [e] at h
  exact h

section Meas

/- English proof (translation)
Establish `hTR : IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Establish `: BorelSpace (WO (reS S b) T)` using `⟨rfl⟩`. Set `eA : WO (reS S b) T ≃+ WO S T` to `{ toFun := reW S T b invFun := reWinv S T b left_inv := reWinv_reW S T b right_inv := reW_reWinv S T b map_add' := reW_add S T b }`. Set `eM : WO (reS S b) T ≃ᵐ WO S T` to `(reWHomeo S T b).toMeasurableEquiv`.

Use `⟨AddEquiv.isAddHaarMeasure_map μ eA (reW_continuous S T b) (reWinv_continuous S T b), ?_⟩` and prove the remaining obligations. Establish `hmp : MeasurePreserving eM μ (μ.map eM)` using `⟨eM.measurable, rfl⟩`. Establish `hmp' : MeasurePreserving eM.symm (μ.map eM) μ` using `MeasurePreserving.symm eM hmp`. Set `eG : ratL T (reS S b) → ratL T S` to `fun g => ⟨reW S T b g, (mem_ratL_reW S T b _).2 g.2⟩`. Establish `hbij : Function.Bijective eG`.

Use `⟨fun g g' hg => ?_, fun g => ⟨⟨reWinv S T b g, (mem_ratL_reW S T b _).1 (by rw [reW_reWinv]; exact g.2)⟩, ?_⟩⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun x : ratL T S => reWinv S T b (x : WO S T)) hg`. Simplify using `only [eG, reWinv_reW] at e`. Conclude with `Subtype.ext e`. Conclude with `Subtype.ext (reW_reWinv S T b _)`.

Use `h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_` and prove the remaining obligations. Use `show reWinv S T b (reW S T b g + x) = (g : WO (reS S b) T) + reWinv S T b x`. Rewrite using `[reWinv_add, reWinv_reW]`.
-/
theorem reW_fd (μ : Measure (WO (reS S b) T)) (𝓕 : Set (WO (reS S b) T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T (reS S b)) 𝓕 μ) :
    (μ.map (reW S T b)).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL T S) (reWinv S T b ⁻¹' 𝓕) (μ.map (reW S T b)) := by
  have hTR : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : BorelSpace (WO (reS S b) T) := ⟨rfl⟩
  let eA : WO (reS S b) T ≃+ WO S T :=
    { toFun := reW S T b
      invFun := reWinv S T b
      left_inv := reWinv_reW S T b
      right_inv := reW_reWinv S T b
      map_add' := reW_add S T b }
  let eM : WO (reS S b) T ≃ᵐ WO S T := (reWHomeo S T b).toMeasurableEquiv
  refine ⟨AddEquiv.isAddHaarMeasure_map μ eA (reW_continuous S T b) (reWinv_continuous S T b), ?_⟩
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL T (reS S b) → ratL T S := fun g => ⟨reW S T b g, (mem_ratL_reW S T b _).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨reWinv S T b g, (mem_ratL_reW S T b _).1 (by rw [reW_reWinv]; exact g.2)⟩, ?_⟩⟩
    · have e := congrArg (fun x : ratL T S => reWinv S T b (x : WO S T)) hg
      simp only [eG, reWinv_reW] at e
      exact Subtype.ext e
    · exact Subtype.ext (reW_reWinv S T b _)
  refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
  show reWinv S T b (reW S T b g + x) = (g : WO (reS S b) T) + reWinv S T b x
  rw [reWinv_add, reWinv_reW]

/- English proof (translation)
Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Establish `: BorelSpace (WO (reS S b) T)` using `⟨rfl⟩`. Set `eM : WO (reS S b) T ≃ᵐ WO S T` to `(reWHomeo S T b).toMeasurableEquiv`. Establish `hmp : MeasurePreserving eM μ (μ.map eM)` using `⟨eM.measurable, rfl⟩`. Establish `e1` using `hmp.setLIntegral_comp_preimage_emb eM.measurableEmbedding F (reWinv S T b ⁻¹' 𝓕)`.

Establish `hpre : eM ⁻¹' (reWinv S T b ⁻¹' 𝓕) = 𝓕`. Use extensionality with `w`. Use `show reWinv S T b (reW S T b w) ∈ 𝓕 ↔ w ∈ 𝓕`. Rewrite using `[reWinv_reW]`. Rewrite `e1` using `[hpre]`.

Conclude with `e1`.
-/
theorem setLIntegral_reW (μ : Measure (WO (reS S b) T)) (𝓕 : Set (WO (reS S b) T))
    (F : WO S T → ENNReal) :
    ∫⁻ w in 𝓕, F (reW S T b w) ∂μ = ∫⁻ x in reWinv S T b ⁻¹' 𝓕, F x ∂(μ.map (reW S T b)) := by
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : BorelSpace (WO (reS S b) T) := ⟨rfl⟩
  let eM : WO (reS S b) T ≃ᵐ WO S T := (reWHomeo S T b).toMeasurableEquiv
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have e1 := hmp.setLIntegral_comp_preimage_emb eM.measurableEmbedding F (reWinv S T b ⁻¹' 𝓕)
  have hpre : eM ⁻¹' (reWinv S T b ⁻¹' 𝓕) = 𝓕 := by
    ext w
    show reWinv S T b (reW S T b w) ∈ 𝓕 ↔ w ∈ 𝓕
    rw [reWinv_reW]
  rw [hpre] at e1
  exact e1

end Meas

section Weil

def omRe (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ) where
  toFun p := (reFEquiv S T b).toLinearMap ∘ₗ om (reGrp S b p.1, p.2) ∘ₗ (reFEquiv S T b).symm.toLinearMap
  map_one' := by
    ext f x
    show (reFEquiv S T b) ((om (reGrp S b 1, 1)) ((reFEquiv S T b).symm f)) x = f x
    rw [map_one, Prod.mk_one_one, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' p q := by
    ext f x
    simp [Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem omRe_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D (reS S b)) (g : GA D T)
    (f' : WO (reS S b) T → ℂ) :
    omRe S T b om (h, g) f' = reF S T b (om (reGrp S b h, g) ((reFEquiv S T b).symm f')) := rfl

/- English proof (translation)
Establish `e : (reFEquiv S T b).symm (reF S T b f) = f` using `(reFEquiv S T b).symm_apply_apply f`. Rewrite using `[omRe_apply, e]`.
-/
theorem omRe_reF (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D (reS S b)) (g : GA D T)
    (f : WO S T → ℂ) : omRe S T b om (h, g) (reF S T b f) = reF S T b (om (reGrp S b h, g) f) := by
  have e : (reFEquiv S T b).symm (reF S T b f) = f := (reFEquiv S T b).symm_apply_apply f
  rw [omRe_apply, e]

/- English proof (translation)
The claim follows from `(reFEquiv S T b).apply_symm_apply f'`.
-/
theorem reF_symm (f' : WO (reS S b) T → ℂ) : reF S T b ((reFEquiv S T b).symm f') = f' :=
  (reFEquiv S T b).apply_symm_apply f'

/- English proof (translation)
Take `⟨h, g⟩` from `p`. Rewrite using `[omRe_apply]`. Use `isThetaFunO_reF S T b ψ _ (hom.om_pres _ _ (isThetaFunO_of_reF S T b ψ _ ?_))` and prove the remaining obligations. Rewrite using `[reF_symm]`. Conclude with `hf'`.

Use `om_heis h g w₀ f' hf' := by set f := (reFEquiv S T b).symm f' with hf`. Establish `hf1 : f' = reF S T b f` using `(reF_symm S T b f').symm`. Establish `hth : IsThetaFunO ψ S T f` using `isThetaFunO_of_reF S T b ψ _ (by rw [← hf1]; exact hf')`. Rewrite using `[hf1, heisO_reF, omRe_reF, omRe_reF, hom.om_heis _ _ _ _ hth, ← reW_actO, heisO_reF]`. Use `om_aut γ hγ γ' hγ' f' hf' := by`.

Establish `hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f')` using `isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')`. Rewrite using `[omRe_apply, reF_apply, reW_zero, hom.om_aut _ (reGrp_mem_GQ S b γ hγ) _ hγ' _ hth]`. Use `conv_rhs => rw [← reF_symm S T b f']`. Conclude with `(reF_zero b _).symm`. Use `om_unit μ 𝓕 hμ h𝓕 p f' hf' := by`.

Take `⟨h, g⟩` from `p`. Establish `hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f')` using `isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')`. Take `⟨hν, h𝓕'⟩` from `reW_fd S T b μ 𝓕 hμ h𝓕`. Establish `e1` using `setLIntegral_reW S T b μ 𝓕 fun x => ‖om (reGrp S b h, g) ((reFEquiv S T b).symm f') x‖ₑ ^ 2`. Establish `e2` using `setLIntegral_reW S T b μ 𝓕 fun x => ‖(reFEquiv S T b).symm f' x‖ₑ ^ 2`.

Establish `e3` using `hom.om_unit _ _ hν h𝓕' (reGrp S b h, g) _ hth`. Establish `e4 : (fun w => ‖f' w‖ₑ ^ 2) = fun w => ‖(reFEquiv S T b).symm f' (reW S T b w)‖ₑ ^ 2`. Use function extensionality and compare the values at `w`. Use `conv_lhs => rw [← reF_symm S T b f']`. Both sides reduce to the same expression.

Rewrite using `[e4]`. Conclude with `e1.trans (e3.trans e2.symm)`.
-/
theorem isWeak_omRe (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (hom : IsWeak ψ S T om) : IsWeak ψ (reS S b) T (omRe S T b om) where
  om_pres p f' hf' := by
    obtain ⟨h, g⟩ := p
    rw [omRe_apply]
    refine isThetaFunO_reF S T b ψ _ (hom.om_pres _ _ (isThetaFunO_of_reF S T b ψ _ ?_))
    rw [reF_symm]; exact hf'
  om_heis h g w₀ f' hf' := by
    set f := (reFEquiv S T b).symm f' with hf
    have hf1 : f' = reF S T b f := (reF_symm S T b f').symm
    have hth : IsThetaFunO ψ S T f := isThetaFunO_of_reF S T b ψ _ (by rw [← hf1]; exact hf')
    rw [hf1, heisO_reF, omRe_reF, omRe_reF, hom.om_heis _ _ _ _ hth, ← reW_actO, heisO_reF]
  om_aut γ hγ γ' hγ' f' hf' := by
    have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
      isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
    rw [omRe_apply, reF_apply, reW_zero, hom.om_aut _ (reGrp_mem_GQ S b γ hγ) _ hγ' _ hth]
    conv_rhs => rw [← reF_symm S T b f']
    exact (reF_zero b _).symm
  om_unit μ 𝓕 hμ h𝓕 p f' hf' := by
    obtain ⟨h, g⟩ := p
    have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
      isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
    obtain ⟨hν, h𝓕'⟩ := reW_fd S T b μ 𝓕 hμ h𝓕
    have e1 := setLIntegral_reW S T b μ 𝓕 fun x => ‖om (reGrp S b h, g) ((reFEquiv S T b).symm f') x‖ₑ ^ 2
    have e2 := setLIntegral_reW S T b μ 𝓕 fun x => ‖(reFEquiv S T b).symm f' x‖ₑ ^ 2
    have e3 := hom.om_unit _ _ hν h𝓕' (reGrp S b h, g) _ hth
    have e4 : (fun w => ‖f' w‖ₑ ^ 2) = fun w => ‖(reFEquiv S T b).symm f' (reW S T b w)‖ₑ ^ 2 := by
      funext w
      conv_lhs => rw [← reF_symm S T b f']
      rfl
    rw [e4]
    exact e1.trans (e3.trans e2.symm)

/- English proof (translation)
Introduce `f' hf' w`. Establish `hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f')` using `isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')`. Establish `e : (fun g : GA D T => omRe S T b om (1, g) f' w) = fun g => om (1, g) ((reFEquiv S T b).symm f') (reW S T b w)`. Use function extensionality and compare the values at `g`. Rewrite using `[omRe_apply, reF_apply, map_one]`.

Rewrite using `[e]`. Conclude with `hc _ hth _`.
-/
theorem contT_omRe (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (hc : ContT ψ om) : ContT ψ (omRe S T b om) := by
  intro f' hf' w
  have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
    isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
  have e : (fun g : GA D T => omRe S T b om (1, g) f' w) =
      fun g => om (1, g) ((reFEquiv S T b).symm f') (reW S T b w) := by
    funext g
    rw [omRe_apply, reF_apply, map_one]
  rw [e]
  exact hc _ hth _

end Weil

/- English proof (translation)
Introduce `D S T b`. Conclude with `⟨reGrp S b, reGrp_mem_GinfC S b, fun ψ om hom hc => ⟨omRe S T b om, isWeak_omRe S T b ψ om hom, contT_omRe S T b ψ om hc, fun h g f => omRe_reF S T b om h g f⟩⟩`.
-/
theorem reframe_weil : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V),
    ∃ e : GA D (reS S b) ≃* GA D S, (∀ h, e h ∈ GinfC S ↔ h ∈ GinfC (reS S b)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
        IsWeak ψ S T om → ContT ψ om →
        ∃ om' : GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ),
          IsWeak ψ (reS S b) T om' ∧ ContT ψ om' ∧
            ∀ h g f, om' (h, g) (reF S T b f) = reF S T b (om (e h, g) f) := by
  intro D S T b
  exact ⟨reGrp S b, reGrp_mem_GinfC S b, fun ψ om hom hc =>
    ⟨omRe S T b om, isWeak_omRe S T b ψ om hom, contT_omRe S T b ψ om hc, fun h g f => omRe_reF S T b om h g f⟩⟩

end GlobalTheory.AdSpan
