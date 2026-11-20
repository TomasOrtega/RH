import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.TanSec.Glue

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.DualPull
open GlobalTheory.Twist (resM resM_resM resM_self app_resM resM_smul)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

/- English proof (translation)
Use `OmegaGlobal.isQuasicoherent_of_frames h` as an intermediate fact. Establish `: (VB.dual F).IsQuasicoherent` using `OmegaGlobal.isQuasicoherent_of_frames fun x =>`. Establish `⟨U, n, _, hx, he⟩` using `h x`. Use the proof step `⟨U, n, _, hx, he.dual⟩`. Use `choose U n e hx he using h`.

Use `Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y)) (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_` and prove the remaining obligations. Establish `H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y))) ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i` using `dual_pull_ext g le_rfl fun W hW S hS e' s => by`. Rewrite using `[dualApp_theta g _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]`. Conclude with `((he (g y)).pullback_basis_repr g hW e' s i).symm`. Establish `: QCoh.appLinear (theta g F) W = (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap` using `(((he (g y)).dual.pullback g).basis hW).ext fun i => by`.

Rewrite using `[IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← H]`. Conclude with `Twist.app_resM (theta g F) hW _`. Rewrite using `[← QCoh.coe_appLinear, this]`. Conclude with `LinearEquiv.bijective _`.
-/
theorem isIso_theta_of_frames {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ VB.IsFrame e) : IsIso (theta g F) := by
  have := OmegaGlobal.isQuasicoherent_of_frames h
  have : (VB.dual F).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := h x
    ⟨U, n, _, hx, he.dual⟩
  choose U n e hx he using h
  refine Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y))
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_
  have H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y)))
      ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i :=
    dual_pull_ext g le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta g _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact ((he (g y)).pullback_basis_repr g hW e' s i).symm
  have : QCoh.appLinear (theta g F) W =
      (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap :=
    (((he (g y)).dual.pullback g).basis hW).ext fun i => by
      rw [IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← H]
      exact Twist.app_resM (theta g F) hW _
  rw [← QCoh.coe_appLinear, this]
  exact LinearEquiv.bijective _

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `e` using `Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j) (Scheme.Modules.pullbackPushforwardAdjunction j) M`. Establish `e' : ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ j ''ᵁ ⊤) (resM M (j.image_preimage_le _) s) = ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app _ s` using `congr(($e).app (j ''ᵁ ⊤) s)`. Rewrite using `[pullbackSections_apply, ← e']`. Use `Eq.trans (congrArg _ ?_) (app_resM _ (j.preimage_image_eq ⊤).ge _)` and prove the remaining obligations. Conclude with `((resM_resM (j.image_preimage_le _) (j.image_mono (j.preimage_image_eq ⊤).ge) s).trans (resM_self _ _)).symm`.
-/
theorem restrict_iso_app {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (s : Γ(M, j ''ᵁ ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app ⊤ s =
      pullbackSections j M (j.preimage_image_eq ⊤).ge s := by
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) M
  have e' : ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ j ''ᵁ ⊤)
      (resM M (j.image_preimage_le _) s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app _ s := congr(($e).app (j ''ᵁ ⊤) s)
  rw [pullbackSections_apply, ← e']
  refine Eq.trans (congrArg _ ?_) (app_resM _ (j.preimage_image_eq ⊤).ge _)
  exact ((resM_resM (j.image_preimage_le _) (j.image_mono (j.preimage_image_eq ⊤).ge) s).trans (resM_self _ _)).symm

/- English proof (translation)
Rewrite using `[← dualApp_theta j _ hW (j.preimage_image_eq ⊤).ge le_top hT, ← restrict_iso_app]`. Establish `e₀ : secOf j M ψ = ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app (dual M)).app ⊤ ((inv (theta j M)).app ⊤ ((homGlobalEquiv _ _).symm ψ))` using `dif_pos hM`. Rewrite using `[e₀]`. Establish `e₁` using `((Scheme.Modules.restrictFunctorIsoPullback j).app (dual M)).inv_hom_id`. Establish `e₂` using `IsIso.inv_hom_id (theta j M)`.

Establish `e₃` using `congr(($e₁).app ⊤ ((inv (theta j M)).app ⊤ ((homGlobalEquiv _ _).symm ψ)))`. Establish `e₄` using `congr(($e₂).app ⊤ ((homGlobalEquiv _ _).symm ψ))`. Conclude with `congrArg (fun l => dualApp l le_top (pullbackSections j M hT s)) ((congrArg ((theta j M).app ⊤) e₃).trans e₄)`.
-/
theorem appLE_dualApp_secOf {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (hM : IsIso (theta j M))
    (ψ : (Scheme.Modules.pullback j).obj M ⟶ structureModule Y) {W : X.Opens} (hW : W ≤ j ''ᵁ ⊤) {T : Y.Opens}
    (hT : T ≤ j ⁻¹ᵁ W) (s : Γ(M, W)) :
    j.appLE W T hT (dualApp (secOf j M ψ) hW s) = (ψ.app T (pullbackSections j M hT s) : Γ(Y, T)) := by
  rw [← dualApp_theta j _ hW (j.preimage_image_eq ⊤).ge le_top hT, ← restrict_iso_app]
  have e₀ : secOf j M ψ = ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app (dual M)).app ⊤
      ((inv (theta j M)).app ⊤ ((homGlobalEquiv _ _).symm ψ)) := dif_pos hM
  rw [e₀]
  have e₁ := ((Scheme.Modules.restrictFunctorIsoPullback j).app (dual M)).inv_hom_id
  have e₂ := IsIso.inv_hom_id (theta j M)
  have e₃ := congr(($e₁).app ⊤ ((inv (theta j M)).app ⊤ ((homGlobalEquiv _ _).symm ψ)))
  have e₄ := congr(($e₂).app ⊤ ((homGlobalEquiv _ _).symm ψ))
  exact congrArg (fun l => dualApp l le_top (pullbackSections j M hT s)) ((congrArg ((theta j M).app ⊤) e₃).trans e₄)

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

/- English proof (translation)
The claim follows from `dif_pos ⟨hv.1, epsZero_comp_of_isTanAtG t hv⟩`.
-/
theorem tanMor_eq (hv : IsTanAtG t x v) : tanMor t.G x v = tanForm t hv :=
  dif_pos ⟨hv.1, epsZero_comp_of_isTanAtG t hv⟩

variable {k' : Type} [Field k'] (φ : k →+* k')

/- English proof (translation)
Use `t.semi` as an intermediate fact. Establish `key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧ resG (Sp k') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) = resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE T₀ ⊤ h₀ ((tanForm t hv).app T₀ (pullbackSections x (omega …`. Take `⟨U, W, hU, hle, c⟩` from `exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V) (x := x (spMap φ y.1)) (h (h₀ trivial))`. Take `⟨T, hT, hyT, hTU₀⟩` from `QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U ⊓ T₀) (spMap φ y.1) ⟨hU, h₀ trivial⟩`. Establish `hTU : T ≤ x ⁻¹ᵁ U` using `hTU₀.trans inf_le_left`.

Establish `hT₀ : T ≤ T₀` using `hTU₀.trans inf_le_right`. Take `⟨f, hf⟩` from `c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle s)`. Establish `hf' : dUnit t.G c.le f = resM (omega t.G) hle s` using `hf`. Establish `hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U` using `(spMap φ).preimage_mono hTU`. Take `⟨⟨a, b⟩, e⟩` from `(bijective_add_mul_epsFn k T hT).2 (v.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)`.

Establish `e₁` using `tanForm_dUnit t hv c.le hTU f a b e.symm`. Establish `kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤ spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T` using `(le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl`. Establish `kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤ ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T` using `le_rfl`. Establish `n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) = (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z)` using `(appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm`. Establish `n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) = resG _ le_top (epsFn k')` using `(appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans (congrArg _ (spMap_dualMap_epsFn φ)))`.

Establish `e₂` using `tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a) ((spMap φ).appLE T _ le_rfl b) (by`. Use `(appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) kk _ f).symm.trans ?_` and prove the remaining obligations. Use `(congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) e.symm).trans ?_` and prove the remaining obligations. Use `(map_add _ _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))`.

Rewrite `e₁`, `e₂` using `[hf', QCoh.pullbackSections_res]`. Use `⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩` and prove the remaining obligations. Use `(app_resM (tanForm t hv') le_top _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[QCoh.res_pullbackSections, e₂, ← e₁]`. Use `.trans ?_ ((appLE_resG (spMap φ) hT₀ le_rfl _).trans (resG_appLE (spMap φ) le_top h₀ _).symm)` and prove the remaining obligations.

Use `congrArg _ ?_` and prove the remaining obligations. Use `.trans ?_ (app_resM (tanForm t hv) hT₀ _)` and prove the remaining obligations. Rewrite using `[QCoh.res_pullbackSections]`. Use `choose T hT hs using key`. Conclude with `LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs`.
-/
theorem tanForm_bc {V : X.Opens} {T₀ : (Sp k).Opens} (h : T₀ ≤ x ⁻¹ᵁ V) (h₀ : ⊤ ≤ spMap φ ⁻¹ᵁ T₀) (hv : IsTanAtG t x v)
    (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V)
    (s : Γ(omega t.G, V)) :
    ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      (spMap φ).appLE T₀ ⊤ h₀ ((tanForm t hv).app T₀ (pullbackSections x (omega t.G) h s) : Γ(Sp k, T₀)) := by
  have := t.semi
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE T₀ ⊤ h₀
        ((tanForm t hv).app T₀ (pullbackSections x (omega t.G) h s) : Γ(Sp k, T₀))) := by
    obtain ⟨U, W, hU, hle, c⟩ := exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V)
      (x := x (spMap φ y.1)) (h (h₀ trivial))
    obtain ⟨T, hT, hyT, hTU₀⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U ⊓ T₀) (spMap φ y.1) ⟨hU, h₀ trivial⟩
    have hTU : T ≤ x ⁻¹ᵁ U := hTU₀.trans inf_le_left
    have hT₀ : T ≤ T₀ := hTU₀.trans inf_le_right
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle s)
    have hf' : dUnit t.G c.le f = resM (omega t.G) hle s := hf
    have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      (v.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)
    have e₁ := tanForm_dUnit t hv c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_dualMap_epsFn φ)))
    have e₂ := tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a)
      ((spMap φ).appLE T _ le_rfl b) (by
        refine (appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (tanForm t hv') le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap φ) hT₀ le_rfl _).trans
      (resG_appLE (spMap φ) le_top h₀ _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (tanForm t hv) hT₀ _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

/- English proof (translation)
Substitute `hg` using the available equality. Take `rfl : spMap φ ≫ j ≫ π = y` from `(Category.assoc _ _ _).symm.trans hy`. Establish `h₀ : ⊤ ≤ spMap φ ⁻¹ᵁ j ⁻¹ᵁ T` using `hgT`. Establish `h₁ : j ⁻¹ᵁ T ≤ (j ≫ π) ⁻¹ᵁ V` using `j.preimage_mono hTV`. Establish `e` using `Vert.DivPull.pullbackComp_inv_app j π (omega t.G) hTV le_rfl h₁ s`.

Establish `e₁` using `((Scheme.Modules.pullbackComp j π).app (omega t.G)).inv_hom_id`. Establish `e₂ : ((Scheme.Modules.pullbackComp j π).hom.app (omega t.G)).app _ (((Scheme.Modules.pullbackComp j π).inv.app (omega t.G)).app _ (pullbackSections (j ≫ π) _ h₁ s)) = pullbackSections (j ≫ π) _ h₁ s` using `congr(($e₁).app _ (pullbackSections (j ≫ π) _ h₁ s))`. Rewrite `e₂` using `[e]`. Establish `e₃` using `appLE_dualApp_secOf j _ hM ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v) hT le_rfl (pullbackSections π _ hTV s)`. Establish `e₄ : ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v).app (j ⁻¹ᵁ T) (pullbackSections j _ le_rfl (pullbackSections π _ hTV s)) = (tanForm t hv).app (j ⁻¹ᵁ T) (pullbackSections (j ≫ π) _ h₁ s)`.

Rewrite using `[tanMor_eq _ hv, ← e₂]`. Both sides reduce to the same expression. Rewrite using `[tanEv, tanForm_bc t φ h₁ h₀ hv hv' hV s, ← appLE_appLE (f := spMap φ) (g := j) rfl le_rfl h₀ hgT, e₃, e₄]`.
-/
theorem appLE_dualApp_secOf_tanMor {Z : Scheme.{0}} (j : Sp k ⟶ Z) [IsOpenImmersion j] (π : Z ⟶ X)
    (hM : IsIso (theta j ((Scheme.Modules.pullback π).obj (omega t.G)))) (hv : IsTanAtG t (j ≫ π) v)
    {g : Sp k' ⟶ Z} (hg : spMap φ ≫ j = g) {y : Sp k' ⟶ X} (hy : g ≫ π = y)
    (hv' : IsTanAtG t y (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) {V : X.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V)
    (s : Γ(omega t.G, V)) {T : Z.Opens} (hT : T ≤ j ''ᵁ ⊤) (hTV : T ≤ π ⁻¹ᵁ V) (hgT : ⊤ ≤ g ⁻¹ᵁ T) :
    (Scheme.ΓSpecIso (.of k')).hom (g.appLE T ⊤ hgT (dualApp (secOf j _
      ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v)) hT (pullbackSections π _ hTV s))) =
      tanEv t hv' hV s := by
  subst hg
  obtain rfl : spMap φ ≫ j ≫ π = y := (Category.assoc _ _ _).symm.trans hy
  have h₀ : ⊤ ≤ spMap φ ⁻¹ᵁ j ⁻¹ᵁ T := hgT
  have h₁ : j ⁻¹ᵁ T ≤ (j ≫ π) ⁻¹ᵁ V := j.preimage_mono hTV
  have e := Vert.DivPull.pullbackComp_inv_app j π (omega t.G) hTV le_rfl h₁ s
  have e₁ := ((Scheme.Modules.pullbackComp j π).app (omega t.G)).inv_hom_id
  have e₂ : ((Scheme.Modules.pullbackComp j π).hom.app (omega t.G)).app _
      (((Scheme.Modules.pullbackComp j π).inv.app (omega t.G)).app _ (pullbackSections (j ≫ π) _ h₁ s)) =
      pullbackSections (j ≫ π) _ h₁ s := congr(($e₁).app _ (pullbackSections (j ≫ π) _ h₁ s))
  rw [e] at e₂
  have e₃ := appLE_dualApp_secOf j _ hM ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v) hT le_rfl
    (pullbackSections π _ hTV s)
  have e₄ : ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v).app (j ⁻¹ᵁ T)
      (pullbackSections j _ le_rfl (pullbackSections π _ hTV s)) =
      (tanForm t hv).app (j ⁻¹ᵁ T) (pullbackSections (j ≫ π) _ h₁ s) := by
    rw [tanMor_eq _ hv, ← e₂]
    rfl
  rw [tanEv, tanForm_bc t φ h₁ h₀ hv hv' hV s, ← appLE_appLE (f := spMap φ) (g := j) rfl le_rfl h₀ hgT, e₃, e₄]

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `TanPair.exists_tanM_equiv _ _ _ t k _ V hV n m hm`. Use `(LieMet.isComb_iff (fun i => LieMet.tanOf (hu i)) _ (LieMet.tanOf hv)).2 (Φ.injective (funext fun b => ?_))` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_apply, hΦ]`. Use `(H b).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, hΦ]`.

Both sides reduce to the same expression.
-/
theorem isCombAtG_of_tanEv {V : X.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {m : Fin n → Γ(omega t.G, V)} (hm : VB.IsFrame m)
    {r : ℕ} {u : Fin r → (Sp (DualNumber k) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x (u i)) (hv : IsTanAtG t x v)
    (c : Fin r → k) (H : ∀ b, tanEv t hv hV (m b) = ∑ i, c i * tanEv t (hu i) hV (m b)) : IsCombAtG t x u c v := by
  obtain ⟨Φ, hΦ⟩ := TanPair.exists_tanM_equiv _ _ _ t k _ V hV n m hm
  refine (LieMet.isComb_iff (fun i => LieMet.tanOf (hu i)) _ (LieMet.tanOf hv)).2
    (Φ.injective (funext fun b => ?_))
  rw [map_sum, Finset.sum_apply, hΦ]
  refine (H b).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_smul, Pi.smul_apply, hΦ]
  rfl

end Tan

/- English proof (translation)
Use `conv_lhs => rw [← (he.basis inf_le_left).sum_repr (resM F inf_le_right (s j))]`. Rewrite using `[map_sum, dualApp_sum, LinearMap.sum_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.Hom.app_smul, dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul, appLE_resG, IsFrame.basis_apply, valF, dif_pos (hw.trans (w.preimage_mono hT))]`. Both sides reduce to the same expression.
-/
theorem val_eq_sum_coef {X : Scheme.{0}} {F P : X.Modules} (θ : F ⟶ dual P) {r : ℕ} {V V' : X.Opens}
    {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')} (he : VB.IsFrame e) (hs : VB.IsFrame s) {k : Type} [Field k]
    (w : Sp k ⟶ X) {T : X.Opens} (hT : T ≤ V ⊓ V') (hw : ⊤ ≤ w ⁻¹ᵁ T) (μ : Γ(P, T)) (j : Fin r) :
    (Scheme.ΓSpecIso (.of k)).hom (w.appLE T ⊤ hw (dualApp (θ.app _ (resM F inf_le_right (s j))) hT μ)) =
      ∑ i, valF w _ (ChainPts.coef false he hs i j) *
        (Scheme.ΓSpecIso (.of k)).hom (w.appLE T ⊤ hw (dualApp (θ.app _ (resM F inf_le_left (e i))) hT μ)) := by
  conv_lhs => rw [← (he.basis inf_le_left).sum_repr (resM F inf_le_right (s j))]
  rw [map_sum, dualApp_sum, LinearMap.sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul, appLE_resG,
    IsFrame.basis_apply, valF, dif_pos (hw.trans (w.preimage_mono hT))]
  rfl

section Mdl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : LocM.Mdl Y i₀)

/- English proof (translation)
Use `(Y Z.i).t.semi` as an intermediate fact. Use `(Y Z.i).t.semi.smooth` as an intermediate fact. Use `isIso_theta_of_frames g fun x => ?_` and prove the remaining obligations. Take `⟨U, n, s, hx, hs⟩` from `exists_isFrame_omega (Y Z.i).t.G (Z.π x)`. Conclude with `⟨_, n, _, hx, hs.pullback Z.π⟩`.
-/
theorem isIso_theta_om {C : Scheme.{0}} (g : C ⟶ Z.X) : IsIso (theta g (om Z)) := by
  have := (Y Z.i).t.semi
  have := (Y Z.i).t.semi.smooth
  refine isIso_theta_of_frames g fun x => ?_
  obtain ⟨U, n, s, hx, hs⟩ := exists_isFrame_omega (Y Z.i).t.G (Z.π x)
  exact ⟨_, n, _, hx, hs.pullback Z.π⟩

/- English proof (translation)
The claim follows from `appLE_dualApp_secOf_tanMor (Y Z.i).t φ (Z.chart a) Z.π (isIso_theta_om Z _) hv hg hy hv' hV s (hT.trans (chart_image_top Z a).ge) hTV hgT`.
-/
theorem appLE_dualApp_sec (a : Fin Z.m) {v : Sp (DualNumber Γ(Z.X, (Z.U a).1)) ⟶ (Y Z.i).t.G.left}
    (hv : IsTanAtG (Y Z.i).t (Z.chart a ≫ Z.π) v) {k : Type} [Field k] (φ : Γ(Z.X, (Z.U a).1) →+* k) {g : Sp k ⟶ Z.X}
    (hg : spMap φ ≫ Z.chart a = g) {y : Sp k ⟶ (Y Z.i).X} (hy : g ≫ Z.π = y)
    (hv' : IsTanAtG (Y Z.i).t y (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) {V : (Y Z.i).X.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V)
    (s : Γ(omega (Y Z.i).t.G, V)) {T : Z.X.Opens} (hT : T ≤ (Z.U a).1) (hTV : T ≤ Z.π ⁻¹ᵁ V) (hgT : ⊤ ≤ g ⁻¹ᵁ T) :
    (Scheme.ΓSpecIso (.of k)).hom (g.appLE T ⊤ hgT (dualApp (TanSec.sec Z a v) hT (pullbackSections Z.π _ hTV s))) =
      tanEv (Y Z.i).t hv' hV s :=
  appLE_dualApp_secOf_tanMor (Y Z.i).t φ (Z.chart a) Z.π (isIso_theta_om Z _) hv hg hy hv' hV s
    (hT.trans (chart_image_top Z a).ge) hTV hgT

end Mdl

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z X h r x _ hfr k _ w a a' φ φ' hφ hφ' j`. Use `(Y Z.i).t.semi` as an intermediate fact. Use `(Y Z.i).t.semi.smooth` as an intermediate fact. Establish `hpt {S : Scheme.{0}} (g : Sp k ⟶ S) {U : S.Opens} (hU : g default ∈ U) : ⊤ ≤ g ⁻¹ᵁ U` using `fun q _ => by`. Rewrite using `[Subsingleton.elim q default]`.

Conclude with `hU`. Establish `hch (b : Fin Z.m) (ψ : Γ(Z.X, (Z.U b).1) →+* k) (hψ : spMap ψ ≫ Z.chart b = w ≫ h) : (w ≫ h) default ∈ (Z.U b).1`. Rewrite using `[← hψ]`. Conclude with `(chart_image_top Z b).le ⟨spMap ψ default, trivial, rfl⟩`. Establish `htan (b : Fin Z.m) (ψ : Γ(Z.X, (Z.U b).1) →+* k) (hψ : spMap ψ ≫ Z.chart b = w ≫ h) (i : Fin r) : IsTanAtG (Y Z.i).t (w ≫ h ≫ Z.π) ((Z.fr b).bc ψ (x i).1 (x i).2)` using `LieMet.isTan_map ψ (by rw [← Category.assoc, hψ, Category.assoc]) ((Z.frame b).1 _ _).1`.

Take `⟨V, n, m, hx, hm⟩` from `exists_isFrame_omega (Y Z.i).t.G ((w ≫ h ≫ Z.π) default)`. Establish `hV` using `hpt _ hx`. Use `isCombAtG_of_tanEv _ hV hm (htan a φ hφ) (htan a' φ' hφ' j) _ fun b => ?_` and prove the remaining obligations. Set `T : Z.X.Opens` to `((Z.U a).1 ⊓ (Z.U a').1) ⊓ Z.π ⁻¹ᵁ V`. Establish `hgT : ⊤ ≤ (w ≫ h) ⁻¹ᵁ T` using `hpt _ ⟨⟨hch a φ hφ, hch a' φ' hφ'⟩, hx⟩`.

Establish `hwT : ⊤ ≤ w ⁻¹ᵁ h ⁻¹ᵁ T` using `hgT`. Establish `hT' : h ⁻¹ᵁ T ≤ h ⁻¹ᵁ (Z.U a).1 ⊓ h ⁻¹ᵁ (Z.U a').1` using `le_inf (h.preimage_mono (inf_le_left.trans inf_le_left)) (h.preimage_mono (inf_le_left.trans inf_le_right))`. Set `μ : Γ(om Z, T)` to `pullbackSections Z.π _ inf_le_right (m b)`. Set `L : Γ(lieX Z h, h ⁻¹ᵁ (Z.U a).1 ⊓ h ⁻¹ᵁ (Z.U a').1) → k` to `fun σ => (Scheme.ΓSpecIso (.of k)).hom (w.appLE _ ⊤ hwT (dualApp ((theta h (om Z)).app _ σ) hT' (pullbackSections h (om Z) le_rfl μ)))`. Establish `hL (c : Fin Z.m) (ψ : Γ(Z.X, (Z.U c).1) →+* k) (hψ : spMap ψ ≫ Z.chart c = w ≫ h) (i : Fin r) (hc : T ≤ (Z.U c).1) (hc' : h ⁻¹ᵁ (Z.U a).1 ⊓ h ⁻¹ᵁ (Z.U a').1 ≤ h ⁻¹ᵁ (Z.U c).1) : L (resM _ hc' (secX Z h x c i)) = tanEv _ (htan c ψ hψ i) hV (m b)`.

Establish `e : resM _ hc' (secX Z h x c i) = pullbackSections h _ hc' (TanSec.sec Z c (Z.fr c (x i).1 (x i).2))` using `res_pullbackSections h _ _ _ _`. Rewrite using `[e]`. Use `Eq.trans (congrArg (Scheme.ΓSpecIso (.of k)).hom ?_) (appLE_dualApp_sec Z c ((Z.frame c).1 _ _).1 ψ hψ (Category.assoc _ _ _) (htan c ψ hψ i) hV (m b) hc inf_le_right hgT)` and prove the remaining obligations. Conclude with `(congrArg (w.appLE _ ⊤ hwT) (dualApp_theta h _ hc hc' hT' le_rfl μ)).trans (appLE_appLE rfl _ _ _ _)`. Rewrite using `[← hL a' φ' hφ' j (inf_le_left.trans inf_le_right) inf_le_right]`.

Use `(val_eq_sum_coef (theta h (om Z)) (hfr a) (hfr a') w hT' hwT _ j).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Conclude with `congrArg (_ * ·) (hL a φ hφ i (inf_le_left.trans inf_le_left) inf_le_left)`.
-/
theorem isCombAtG_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : GlobalTheory.LocM.Mdl Y i₀) (X : Scheme.{0}) (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ∀ (hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a)) (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k), spMap φ ≫ Z.chart a = w ≫ h → spMap φ' ≫ Z.chart a' = w ≫ h → ∀ j, IsCombAtG (Y Z.i).t (w ≫ h ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) (fun i => valF w _ (GlobalTheory.ChainPts.coef false (hfr a) (hfr a') i j)) ((Z.fr a').bc φ' (x j).1 (x j).2) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X h r x _ hfr k _ w a a' φ φ' hφ hφ' j
  have := (Y Z.i).t.semi
  have := (Y Z.i).t.semi.smooth
  have hpt {S : Scheme.{0}} (g : Sp k ⟶ S) {U : S.Opens} (hU : g default ∈ U) : ⊤ ≤ g ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim q default]; exact hU
  have hch (b : Fin Z.m) (ψ : Γ(Z.X, (Z.U b).1) →+* k) (hψ : spMap ψ ≫ Z.chart b = w ≫ h) :
      (w ≫ h) default ∈ (Z.U b).1 := by
    rw [← hψ]
    exact (chart_image_top Z b).le ⟨spMap ψ default, trivial, rfl⟩
  have htan (b : Fin Z.m) (ψ : Γ(Z.X, (Z.U b).1) →+* k) (hψ : spMap ψ ≫ Z.chart b = w ≫ h) (i : Fin r) :
      IsTanAtG (Y Z.i).t (w ≫ h ≫ Z.π) ((Z.fr b).bc ψ (x i).1 (x i).2) :=
    LieMet.isTan_map ψ (by rw [← Category.assoc, hψ, Category.assoc]) ((Z.frame b).1 _ _).1
  obtain ⟨V, n, m, hx, hm⟩ := exists_isFrame_omega (Y Z.i).t.G ((w ≫ h ≫ Z.π) default)
  have hV := hpt _ hx
  refine isCombAtG_of_tanEv _ hV hm (htan a φ hφ) (htan a' φ' hφ' j) _ fun b => ?_
  let T : Z.X.Opens := ((Z.U a).1 ⊓ (Z.U a').1) ⊓ Z.π ⁻¹ᵁ V
  have hgT : ⊤ ≤ (w ≫ h) ⁻¹ᵁ T := hpt _ ⟨⟨hch a φ hφ, hch a' φ' hφ'⟩, hx⟩
  have hwT : ⊤ ≤ w ⁻¹ᵁ h ⁻¹ᵁ T := hgT
  have hT' : h ⁻¹ᵁ T ≤ h ⁻¹ᵁ (Z.U a).1 ⊓ h ⁻¹ᵁ (Z.U a').1 :=
    le_inf (h.preimage_mono (inf_le_left.trans inf_le_left)) (h.preimage_mono (inf_le_left.trans inf_le_right))
  let μ : Γ(om Z, T) := pullbackSections Z.π _ inf_le_right (m b)
  let L : Γ(lieX Z h, h ⁻¹ᵁ (Z.U a).1 ⊓ h ⁻¹ᵁ (Z.U a').1) → k := fun σ =>
    (Scheme.ΓSpecIso (.of k)).hom (w.appLE _ ⊤ hwT
      (dualApp ((theta h (om Z)).app _ σ) hT' (pullbackSections h (om Z) le_rfl μ)))
  have hL (c : Fin Z.m) (ψ : Γ(Z.X, (Z.U c).1) →+* k) (hψ : spMap ψ ≫ Z.chart c = w ≫ h) (i : Fin r)
      (hc : T ≤ (Z.U c).1) (hc' : h ⁻¹ᵁ (Z.U a).1 ⊓ h ⁻¹ᵁ (Z.U a').1 ≤ h ⁻¹ᵁ (Z.U c).1) :
      L (resM _ hc' (secX Z h x c i)) = tanEv _ (htan c ψ hψ i) hV (m b) := by
    have e : resM _ hc' (secX Z h x c i) = pullbackSections h _ hc' (TanSec.sec Z c (Z.fr c (x i).1 (x i).2)) :=
      res_pullbackSections h _ _ _ _
    rw [e]
    refine Eq.trans (congrArg (Scheme.ΓSpecIso (.of k)).hom ?_) (appLE_dualApp_sec Z c ((Z.frame c).1 _ _).1 ψ hψ (Category.assoc _ _ _)
      (htan c ψ hψ i) hV (m b) hc inf_le_right hgT)
    exact (congrArg (w.appLE _ ⊤ hwT) (dualApp_theta h _ hc hc' hT' le_rfl μ)).trans (appLE_appLE rfl _ _ _ _)
  rw [← hL a' φ' hφ' j (inf_le_left.trans inf_le_right) inf_le_right]
  refine (val_eq_sum_coef (theta h (om Z)) (hfr a) (hfr a') w hT' hwT _ j).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact congrArg (_ * ·) (hL a φ hφ i (inf_le_left.trans inf_le_left) inf_le_left)

end GlobalTheory.TanSec.Glue
