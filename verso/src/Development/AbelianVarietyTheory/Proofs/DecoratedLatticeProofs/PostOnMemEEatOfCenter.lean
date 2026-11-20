import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PostOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

set_option maxHeartbeats 800000

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

namespace GlobalTheory.MiTop.CentralShift

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show actG0 V β Ld g0 (rTr V z f) x = actG0 V β Ld g0 f (x * z)`. Unfold `actG0`. Use `split_ifs with hk`. Simplify using `only [rTr]`.

Rewrite using `[mul_assoc x hk.choose z, mul_assoc x z hk.choose, Subgroup.mem_center_iff.mp hz hk.choose]`. Both sides reduce to the same expression.
-/
theorem actL_rTr_of_center (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank) (g0 : G0 Ld.Pg Ld.r)
    {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    actL V β Ld g0 (rTr V z f) = rTr V z (actL V β Ld g0 f) := by
  funext x
  show actG0 V β Ld g0 (rTr V z f) x = actG0 V β Ld g0 f (x * z)
  unfold actG0
  split_ifs with hk
  · simp only [rTr]
    rw [mul_assoc x hk.choose z, mul_assoc x z hk.choose, Subgroup.mem_center_iff.mp hz hk.choose]
  · rfl

/- English proof (translation)
Unfold `gaL`. Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, actL_rTr_of_center β Ld _ hz]`. Simplify using `[rTr, Finset.sum_apply]`.
-/
theorem gaL_rTr_of_center {G : Type} [Group G] [Fintype G] (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 Ld.Pg Ld.r) (c : G → ℂ) {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    gaL V β Ld eG c (rTr V z f) = rTr V z (gaL V β Ld eG c f) := by
  unfold gaL
  funext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, actL_rTr_of_center β Ld _ hz]
  simp [rTr, Finset.sum_apply]

/- English proof (translation)
Establish `e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U'` using `funext fun c => propext (h c)`. Unfold `ipM`. Rewrite using `[e]`.
-/
theorem ipM_eq_of_iff (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {T T' U U' : MMap M}
    (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) : ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

/- English proof (translation)
Establish `e : (fun g : GA D V => g * z) = fun g => z * g` using `funext fun g => Subgroup.mem_center_iff.mp hz g`. Rewrite using `[e]`. Conclude with `map_mul_left_eq_self μ z`.
-/
theorem map_mul_right_center (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) {z : GA D V}
    (hz : z ∈ Subgroup.center (GA D V)) : Measure.map (fun g => g * z) μ = μ := by
  have e : (fun g : GA D V => g * z) = fun g => z * g := funext fun g => Subgroup.mem_center_iff.mp hz g
  rw [e]
  exact map_mul_left_eq_self μ z

/- English proof (translation)
Establish `: PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) = GlobalTheory.FinTranslate.rTrL V z ∘ₗ PiTensorProduct.lift T`. Apply `PiTensorProduct.ext` to reduce the goal to its premises. Use extensionality with `w`. Simplify using `[postOn, PiTensorProduct.lift.tprod]`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem lift_postOn (T : MMap M) (z : GA D V) (v : SmT M) :
    PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) v = rTr V z (PiTensorProduct.lift T v) := by
  have : PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) =
      GlobalTheory.FinTranslate.rTrL V z ∘ₗ PiTensorProduct.lift T := by
    apply PiTensorProduct.ext
    ext w
    simp [postOn, PiTensorProduct.lift.tprod]
  rw [this]
  rfl

end General

section Main

open GlobalTheory.MiTop.CentralShift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

/- English proof (translation)
Unfold `RealDat.EEat at hT ⊢`. Use `GlobalTheory.MultTranslate.postOn_mem_goodPart hzf (fun k hk => ?_) (fun f => ?_) hT` and prove the remaining obligations. Establish `e : z⁻¹ * k * z = k`. Rewrite using `[mul_assoc, Subgroup.mem_center_iff.mp hzc k, inv_mul_cancel_left]`. Rewrite using `[e]`.

Conclude with `⟨hk, rfl⟩`. Unfold `RealDat.e0`. Conclude with `gaL_rTr_of_center _ _ _ _ hzc f`.
-/
theorem postOn_mem_EEat_of_center (W : RealPack ex) {z : GA D (Yc D 0)} (hzf : z ∈ GfC (Yc D 0))
    (hzc : z ∈ Subgroup.center (GA D (Yc D 0))) (Pl : LevelP W.Q.Rl.toRealDat.Pg D.R.r ℂ) {T : MMap (W.Q.Rl.MY 0)}
    (hT : T ∈ W.Q.Rl.toRealDat.EEat Pl) :
    postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) T ∈ W.Q.Rl.toRealDat.EEat Pl := by
  unfold RealDat.EEat at hT ⊢
  refine GlobalTheory.MultTranslate.postOn_mem_goodPart hzf (fun k hk => ?_) (fun f => ?_) hT
  · have e : z⁻¹ * k * z = k := by
      rw [mul_assoc, Subgroup.mem_center_iff.mp hzc k, inv_mul_cancel_left]
    rw [e]
    exact ⟨hk, rfl⟩
  · unfold RealDat.e0
    exact gaL_rTr_of_center _ _ _ _ hzc f

end Main

end GlobalTheory.MiTop.CentralShift

namespace GlobalTheory.MiTop

open GlobalTheory.MiTop.CentralShift

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc`. Establish `hM` using `hB.hyp.2.2.2.1.models`. Establish `hE` using `hM.HE`. Establish `h0` using `hM.ν0`. Establish `hHaar : W.Q.Rl.ν0.IsHaarMeasure` using `h0.1.1`.

Establish `hFD` using `h0.2`. Take `⟨hinj, hrange, hip⟩` from `hE`. Establish `he : ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat W.Q.Rl.toRealDat.triv` using `fun e => by`. Rewrite using `[← hrange]`. Conclude with `LinearMap.mem_range_self _ e`.

Establish `hmem : ∀ e, postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) ∈ LinearMap.range W.Q.Rl.HE.e` using `fun e => by rw [hrange]; exact postOn_mem_EEat_of_center W hzf hzc _ (he e)`. Set `Lr : W.Q.Rl.HE.H →ₗ[ℂ] LinearMap.range W.Q.Rl.HE.e` to `(postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) ∘ₗ W.Q.Rl.HE.e).codRestrict _ hmem`. Set `Vz : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H` to `(LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm.toLinearMap ∘ₗ Lr`. Establish `hV : ∀ e, W.Q.Rl.HE.e (Vz e) = postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e)`. Introduce `e`.

Establish `h1 : ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) : LinearMap.range W.Q.Rl.HE.e) : MMap (W.Q.Rl.MY 0)) = W.Q.Rl.HE.e ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e))` using `LinearEquiv.ofInjective_apply _ _`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1.symm`. Establish `hzc' : z⁻¹ ∈ Subgroup.center (GA D (Yc D 0))` using `Subgroup.inv_mem _ hzc`. Establish `hipv : ∀ e e' : W.Q.Rl.HE.H, ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (W.Q.Rl.HE.e e) (W.Q.Rl.HE.e e') = ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e)) (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL ( …`.

Introduce `e e'`. Establish `m1` using `(Submodule.mem_inf.mp (he e)).1`. Establish `m2` using `(Submodule.mem_inf.mp (he e')).1`. Establish `m3` using `(Submodule.mem_inf.mp (postOn_mem_EEat_of_center W hzf hzc _ (he e))).1`. Establish `m4` using `(Submodule.mem_inf.mp (postOn_mem_EEat_of_center W hzf hzc _ (he e'))).1`.

Apply `ipM_eq_of_iff` to reduce the goal to its premises. Introduce `c`. Prove the components needed by the constructor for the conclusion. Conclude with `GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z 1 (by simp) (map_mul_right_center _ hHaar hzc) _ m1 _ m2 _ _ (fun v g => by rw [one_mul]; rfl) (fun v g => by rw [one_mul]; rfl) c`. Conclude with `GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z⁻¹ 1 (by simp) (map_mul_right_center _ hHaar hzc') _ m3 _ m4 _ _ (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e v) (inv_mul_cancel_right g _).symm) (fun v g => by rw [one_mul]; exact congrArg …`.

Use `⟨Vz, fun e v => ?_, fun e => ?_, fun e hel => ?_⟩` and prove the remaining obligations. Unfold `rowOf`. Rewrite using `[hV]`. Conclude with `lift_postOn _ _ _`. Rewrite using `[@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hip, hip, hV, ← hipv]`.

Rewrite using `[hV]`. Conclude with `postOn_mem_EEat_of_center W hzf hzc _ hel`.
-/
theorem exists_isShift_of_center : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∃ V, IsShift W z V := by
  intro D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc
  have hM := hB.hyp.2.2.2.1.models
  have hE := hM.HE
  have h0 := hM.ν0
  have hHaar : W.Q.Rl.ν0.IsHaarMeasure := h0.1.1
  have hFD := h0.2
  obtain ⟨hinj, hrange, hip⟩ := hE
  have he : ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat W.Q.Rl.toRealDat.triv := fun e => by
    rw [← hrange]; exact LinearMap.mem_range_self _ e
  have hmem : ∀ e, postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) ∈ LinearMap.range W.Q.Rl.HE.e :=
    fun e => by rw [hrange]; exact postOn_mem_EEat_of_center W hzf hzc _ (he e)
  let Lr : W.Q.Rl.HE.H →ₗ[ℂ] LinearMap.range W.Q.Rl.HE.e :=
    (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) ∘ₗ W.Q.Rl.HE.e).codRestrict _ hmem
  let Vz : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H := (LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm.toLinearMap ∘ₗ Lr
  have hV : ∀ e, W.Q.Rl.HE.e (Vz e) = postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) := by
    intro e
    have h1 : ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) : LinearMap.range W.Q.Rl.HE.e) : MMap (W.Q.Rl.MY 0)) =
        W.Q.Rl.HE.e ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) := LinearEquiv.ofInjective_apply _ _
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hzc' : z⁻¹ ∈ Subgroup.center (GA D (Yc D 0)) := Subgroup.inv_mem _ hzc
  have hipv : ∀ e e' : W.Q.Rl.HE.H,
      ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (W.Q.Rl.HE.e e) (W.Q.Rl.HE.e e') =
        ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e))
          (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e')) := by
    intro e e'
    have m1 := (Submodule.mem_inf.mp (he e)).1
    have m2 := (Submodule.mem_inf.mp (he e')).1
    have m3 := (Submodule.mem_inf.mp (postOn_mem_EEat_of_center W hzf hzc _ (he e))).1
    have m4 := (Submodule.mem_inf.mp (postOn_mem_EEat_of_center W hzf hzc _ (he e'))).1
    apply ipM_eq_of_iff
    intro c
    constructor
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z 1 (by simp) (map_mul_right_center _ hHaar hzc)
        _ m1 _ m2 _ _ (fun v g => by rw [one_mul]; rfl) (fun v g => by rw [one_mul]; rfl) c
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z⁻¹ 1 (by simp) (map_mul_right_center _ hHaar hzc')
        _ m3 _ m4 _ _ (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e v) (inv_mul_cancel_right g _).symm)
        (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e' v) (inv_mul_cancel_right g _).symm) c
  refine ⟨Vz, fun e v => ?_, fun e => ?_, fun e hel => ?_⟩
  · unfold rowOf
    rw [hV]
    exact lift_postOn _ _ _
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hip, hip, hV, ← hipv]
  · rw [hV]
    exact postOn_mem_EEat_of_center W hzf hzc _ hel

end GlobalTheory.MiTop

end
