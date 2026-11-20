import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineVectorBundleSectionSeparationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB MonoidalCategory

namespace GlobalTheory.HodgeSubInj

/- English proof (translation)
Establish `e` using `hV.fromSpec_preimage_self.ge`. Use `letI := GlobalTheory.QCoh.appLEAlgebra hV.fromSpec e`. Use `letI := GlobalTheory.QCoh.appLEModule hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e`. Use `haveI := GlobalTheory.QCoh.appLE_isScalarTower hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e`. Establish `H` using `GlobalTheory.QCoh.isBaseChange_pullbackSections hV.fromSpec F (isAffineOpen_top _) hV e`.

Establish `hb : Function.Bijective (Algebra.linearMap Γ(T, V) Γ(Sp Γ(T, V), ⊤))`. Establish `: hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv`. Rewrite using `[Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Conclude with `(congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)`. Express the relevant statement in the definitionally equal form `Function.Bijective (hV.fromSpec.appLE V ⊤ e)`.

Rewrite using `[this]`. Conclude with `ConcreteCategory.bijective_of_isIso _`. Set `φ` to `(LinearEquiv.ofBijective _ hb).symm`. Set `g` to `(TensorProduct.lid Γ(T, V) Γ(F, V)).toLinearMap ∘ₗ LinearMap.rTensor Γ(F, V) φ.toLinearMap`. Establish `hg : ∀ m, g (H.equiv.symm (GlobalTheory.QCoh.pullbackSections hV.fromSpec F e m)) = m`.

Introduce `m`. Establish `h1 : H.equiv.symm (GlobalTheory.QCoh.pullbackSections hV.fromSpec F e m) = (1 : Γ(Sp Γ(T, V), ⊤)) ⊗ₜ m`. Rewrite using `[LinearEquiv.symm_apply_eq, H.equiv_tmul, one_smul]`. Establish `h2 : φ 1 = 1`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Conclude with `(map_one (algebraMap Γ(T, V) Γ(Sp Γ(T, V), ⊤))).symm`. Simplify using `only [g, h1, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, h2, TensorProduct.lid_tmul, one_smul]`. Introduce `m m' hm`. Rewrite using `[← hg m, ← hg m']`. Conclude with `congrArg (fun x => g (H.equiv.symm x)) hm`.
-/
theorem pullbackSections_fromSpec_injective {T : Scheme.{0}} (F : T.Modules) [F.IsQuasicoherent]
    {V : T.Opens} (hV : IsAffineOpen V) :
    Function.Injective (GlobalTheory.QCoh.pullbackSections hV.fromSpec F hV.fromSpec_preimage_self.ge) := by
  have e := hV.fromSpec_preimage_self.ge
  letI := GlobalTheory.QCoh.appLEAlgebra hV.fromSpec e
  letI := GlobalTheory.QCoh.appLEModule hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e
  haveI := GlobalTheory.QCoh.appLE_isScalarTower hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e
  have H := GlobalTheory.QCoh.isBaseChange_pullbackSections hV.fromSpec F (isAffineOpen_top _) hV e
  have hb : Function.Bijective (Algebra.linearMap Γ(T, V) Γ(Sp Γ(T, V), ⊤)) := by
    have : hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv := by
      rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
    change Function.Bijective (hV.fromSpec.appLE V ⊤ e)
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  let φ := (LinearEquiv.ofBijective _ hb).symm
  let g := (TensorProduct.lid Γ(T, V) Γ(F, V)).toLinearMap ∘ₗ LinearMap.rTensor Γ(F, V) φ.toLinearMap
  have hg : ∀ m, g (H.equiv.symm (GlobalTheory.QCoh.pullbackSections hV.fromSpec F e m)) = m := by
    intro m
    have h1 : H.equiv.symm (GlobalTheory.QCoh.pullbackSections hV.fromSpec F e m) = (1 : Γ(Sp Γ(T, V), ⊤)) ⊗ₜ m := by
      rw [LinearEquiv.symm_apply_eq, H.equiv_tmul, one_smul]
    have h2 : φ 1 = 1 := by
      rw [LinearEquiv.symm_apply_eq]
      exact (map_one (algebraMap Γ(T, V) Γ(Sp Γ(T, V), ⊤))).symm
    simp only [g, h1, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, h2,
      TensorProduct.lid_tmul, one_smul]
  intro m m' hm
  rw [← hg m, ← hg m']
  exact congrArg (fun x => g (H.equiv.symm x)) hm

/- English proof (translation)
Establish `: F.IsQuasicoherent` using `hF.isQuasicoherent`. Use `pullbackSections_fromSpec_injective F hV (sub_eq_zero.1 ?_)` and prove the remaining obligations. Use `GlobalTheory.T.affine_vector_bundle_section_separation _ _ r (hF.pullback hV.fromSpec) _ fun L => ?_` and prove the remaining obligations. Rewrite using `[map_sub, H L, sub_self]`.
-/
theorem sep {T : Scheme.{0}} (F : T.Modules) (r : ℕ) (hF : GlobalTheory.VB.IsVB F r) {V : T.Opens}
    (hV : IsAffineOpen V) (s s' : Γ(F, V))
    (H : ∀ L : (Scheme.Modules.pullback hV.fromSpec).obj F ⟶ GlobalTheory.structureModule (Sp Γ(T, V)),
      L.app ⊤ (GlobalTheory.QCoh.pullbackSections hV.fromSpec F hV.fromSpec_preimage_self.ge s) =
        L.app ⊤ (GlobalTheory.QCoh.pullbackSections hV.fromSpec F hV.fromSpec_preimage_self.ge s')) :
    s = s' := by
  have : F.IsQuasicoherent := hF.isQuasicoherent
  refine pullbackSections_fromSpec_injective F hV (sub_eq_zero.1 ?_)
  refine GlobalTheory.T.affine_vector_bundle_section_separation _ _ r (hF.pullback hV.fromSpec) _ fun L => ?_
  rw [map_sub, H L, sub_self]

/- English proof (translation)
Use `⟨Over.homMk (pullback.lift v₀ (epsR Γ(T, V)).hom w) (pullback.lift_snd _ _ _), ?_, pullback.lift_fst _ _ _⟩` and prove the remaining obligations. Establish `hs : spMap (TrivSqZeroExt.fstHom Γ(T, V) Γ(T, V) Γ(T, V)).toRingHom = sec (epsZero Γ(T, V))` using `rfl`. Establish `h1` using `Over.w (MonObj.one : 𝟙_ (Over (Sp Γ(T, V))) ⟶ onAff A hV)`. Establish `h2 : (MonObj.one : 𝟙_ (Over (Sp Γ(T, V))) ⟶ onAff A hV) = Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec) ≫ (Over.pullback hV.fromSpec).map MonObj.one` using `rfl`. Establish `h3` using `Over.w (Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec))`.

Unfold `IsTangent`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Over.homMk_left, Category.assoc, pullback.lift_fst]`. Rewrite using `[hs, we, h2, Over.comp_left, Category.assoc]`. Establish `h4 : ((Over.pullback hV.fromSpec).map (MonObj.one : 𝟙_ (Over T) ⟶ A)).left ≫ pullback.fst A.hom hV.fromSpec = pullback.fst (𝟙_ (Over T)).hom hV.fromSpec ≫ (MonObj.one : 𝟙_ (Over T) ⟶ A).left`.

Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`. Establish `h5 : (Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec)).left ≫ pullback.fst (𝟙_ (Over T)).hom hV.fromSpec = hV.fromSpec`. Establish `c` using `pullback.condition (f := (𝟙_ (Over T)).hom) (g := hV.fromSpec)`. Establish `c' : pullback.fst (𝟙_ (Over T)).hom hV.fromSpec = pullback.snd (𝟙_ (Over T)).hom hV.fromSpec ≫ hV.fromSpec`.

Simplify using `using c`. Rewrite using `[c', ← Category.assoc]`. Establish `h3' : (Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec)).left ≫ pullback.snd (𝟙_ (Over T)).hom hV.fromSpec = 𝟙 _` using `h3`. Rewrite using `[h3', Category.id_comp]`. Rewrite using `[h4, ← Category.assoc, h5]`.

Both sides reduce to the same expression. Simplify using `only [Over.homMk_left, Category.assoc, pullback.lift_snd]`. Rewrite using `[hs, sec_hom]`. Conclude with `h1.symm`.
-/
theorem lift {T : Scheme.{0}} (A : Over T) [GrpObj A] {V : T.Opens} (hV : IsAffineOpen V)
    (v₀ : (Pdiv.specO Γ(T, V) (DualNumber Γ(T, V))).left ⟶ A.left)
    (w : v₀ ≫ A.hom = (Pdiv.specO Γ(T, V) (DualNumber Γ(T, V))).hom ≫ hV.fromSpec)
    (we : sec (epsZero Γ(T, V)) ≫ v₀ = hV.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A) :
    ∃ v : epsR Γ(T, V) ⟶ onAff A hV, IsTangent v ∧ v.left ≫ pullback.fst A.hom hV.fromSpec = v₀ := by
  refine ⟨Over.homMk (pullback.lift v₀ (epsR Γ(T, V)).hom w) (pullback.lift_snd _ _ _), ?_,
    pullback.lift_fst _ _ _⟩
  have hs : spMap (TrivSqZeroExt.fstHom Γ(T, V) Γ(T, V) Γ(T, V)).toRingHom = sec (epsZero Γ(T, V)) := rfl
  have h1 := Over.w (MonObj.one : 𝟙_ (Over (Sp Γ(T, V))) ⟶ onAff A hV)
  have h2 : (MonObj.one : 𝟙_ (Over (Sp Γ(T, V))) ⟶ onAff A hV) =
      Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec) ≫ (Over.pullback hV.fromSpec).map MonObj.one := rfl
  have h3 := Over.w (Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec))
  unfold IsTangent
  apply pullback.hom_ext
  · simp only [Over.homMk_left, Category.assoc, pullback.lift_fst]
    rw [hs, we, h2, Over.comp_left, Category.assoc]
    have h4 : ((Over.pullback hV.fromSpec).map (MonObj.one : 𝟙_ (Over T) ⟶ A)).left ≫
        pullback.fst A.hom hV.fromSpec =
        pullback.fst (𝟙_ (Over T)).hom hV.fromSpec ≫ (MonObj.one : 𝟙_ (Over T) ⟶ A).left := by
      simp only [Over.pullback_map_left]
      exact pullback.lift_fst _ _ _
    have h5 : (Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec)).left ≫
        pullback.fst (𝟙_ (Over T)).hom hV.fromSpec = hV.fromSpec := by
      have c := pullback.condition (f := (𝟙_ (Over T)).hom) (g := hV.fromSpec)
      have c' : pullback.fst (𝟙_ (Over T)).hom hV.fromSpec = pullback.snd (𝟙_ (Over T)).hom hV.fromSpec ≫ hV.fromSpec := by
        simpa using c
      rw [c', ← Category.assoc]
      have h3' : (Functor.LaxMonoidal.ε (Over.pullback hV.fromSpec)).left ≫
          pullback.snd (𝟙_ (Over T)).hom hV.fromSpec = 𝟙 _ := h3
      rw [h3', Category.id_comp]
    rw [h4, ← Category.assoc, h5]
    rfl
  · simp only [Over.homMk_left, Category.assoc, pullback.lift_snd]
    rw [hs, sec_hom]
    exact h1.symm

/- English proof (translation)
Introduce `P T A _ g hA hg V hV s s' c hs hs'`. Establish `hA' : IsAbelianScheme (onAff A hV)` using `GlobalTheory.isAbelianScheme_pullback_obj _ _ hA`. Establish `hg' : SmoothOfRelativeDimension g (onAff A hV).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom hV.fromSpec) hg`. Establish `hLE` using `(P.p5.2.1 Γ(T, V) (onAff A hV) g hA' hg').1`. Establish `: SmoothOfRelativeDimension g A.hom` using `hg`.

Establish `he : GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A ≫ A.hom = 𝟙 T`. Use `Over.w (MonObj.one : 𝟙_ (Over T) ⟶ A)` as an intermediate fact. Simplify `this` using `[GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec]`. Establish `: IsProper A.hom` using `hA.proper`. Establish `: QuasiSeparated A.hom` using `inferInstance`.

Use `sep (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) g (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g) hV s s' fun L => ?_` and prove the remaining obligations. Take `⟨v₀, w, we, rfl⟩` from `GlobalTheory.TanFibre.exists_form_eq he L`. Take `⟨v, hvt, rfl⟩` from `lift A hV v₀ w we`. Take `⟨h, hh⟩` from `hLE.2 v hvt`. Establish `e` using `(hs v h hh w we).symm.trans (hs' v h hh w we)`.

Establish `inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom` using `fun a b hab => by`. Simplify using `using congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).inv hab`. Conclude with `inj e`.
-/
theorem eq_of_corr : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (s s' : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V))
      (c : primDR (onAff A hV)),
      GlobalTheory.HodgeSub.Corr A hV s c → GlobalTheory.HodgeSub.Corr A hV s' c → s = s' := by
  intro P T A _ g hA hg V hV s s' c hs hs'
  have hA' : IsAbelianScheme (onAff A hV) := GlobalTheory.isAbelianScheme_pullback_obj _ _ hA
  have hg' : SmoothOfRelativeDimension g (onAff A hV).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom hV.fromSpec) hg
  have hLE := (P.p5.2.1 Γ(T, V) (onAff A hV) g hA' hg').1
  have : SmoothOfRelativeDimension g A.hom := hg
  have he : GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A ≫ A.hom = 𝟙 T := by
    have := Over.w (MonObj.one : 𝟙_ (Over T) ⟶ A)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec] using this
  have : IsProper A.hom := hA.proper
  have : QuasiSeparated A.hom := inferInstance
  refine sep (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) g (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g) hV s s' fun L => ?_
  obtain ⟨v₀, w, we, rfl⟩ := GlobalTheory.TanFibre.exists_form_eq he L
  obtain ⟨v, hvt, rfl⟩ := lift A hV v₀ w we
  obtain ⟨h, hh⟩ := hLE.2 v hvt
  have e := (hs v h hh w we).symm.trans (hs' v h hh w we)
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom := fun a b hab => by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).inv hab
  exact inj e

end GlobalTheory.HodgeSubInj
