import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHeadWt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBOfChartPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBundleFramesChartsChangeBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyFreeSubsheafDetIsoStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefHodge

def chartwise {X C : Scheme.{0}} (A : LB X) (g : C ⟶ X) : LB C :=
  ⟨A.ι, fun k => g ⁻¹ᵁ A.U k, fun k k' => pullU g (A.U k ⊓ A.U k') (A.g k k')⟩

/- English proof (translation)
Set `a : ChartPull (chartwise A g) (A.pull g) (𝟙 C)` to `⟨fun k _ => k, fun k y hy => mem_pull.2 hy, fun y k k' hk hk' => (gm_pull (𝟙 C) g y (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans (gm_pull_g A g (𝟙 C) y (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).symm⟩`. Use `⟨NefFibre.isLB_of_chartPull a (LB.isLB_pull hA g) fun y => ?_, iso_of_chart (LB.isLB_pull hA g) a⟩` and prove the remaining obligations. Conclude with `(Opens.mem_iSup (s := A.U)).1 (hA.cover.ge (Set.mem_univ (g y)))`.
-/
theorem isLB_chartwise {X C : Scheme.{0}} {A : LB X} (hA : A.IsLB) (g : C ⟶ X) :
    (chartwise A g).IsLB ∧ LBIso (chartwise A g) (A.pull g) := by
  let a : ChartPull (chartwise A g) (A.pull g) (𝟙 C) :=
    ⟨fun k _ => k, fun k y hy => mem_pull.2 hy, fun y k k' hk hk' =>
      (gm_pull (𝟙 C) g y (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
        (gm_pull_g A g (𝟙 C) y (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).symm⟩
  refine ⟨NefFibre.isLB_of_chartPull a (LB.isLB_pull hA g) fun y => ?_, iso_of_chart (LB.isLB_pull hA g) a⟩
  exact (Opens.mem_iSup (s := A.U)).1 (hA.cover.ge (Set.mem_univ (g y)))

open GlobalTheory.VB GlobalTheory.DualPull in

/- English proof (translation)
Use `OmegaGlobal.isQuasicoherent_of_frames h` as an intermediate fact. Establish `: (VB.dual F).IsQuasicoherent` using `OmegaGlobal.isQuasicoherent_of_frames fun x =>`. Establish `⟨U, n, _, hx, he⟩` using `h x`. Use the proof step `⟨U, n, _, hx, he.dual⟩`. Use `choose U n e hx he using h`.

Use `Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y)) (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_` and prove the remaining obligations. Establish `H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y))) ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i` using `dual_pull_ext g le_rfl fun W hW S hS e' s => by`. Rewrite using `[dualApp_theta g _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]`. Conclude with `((he (g y)).pullback_basis_repr g hW e' s i).symm`. Establish `: QCoh.appLinear (theta g F) W = (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap` using `(((he (g y)).dual.pullback g).basis hW).ext fun i => by`.

Rewrite using `[IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← H]`. Conclude with `Twist.app_resM (theta g F) hW _`. Rewrite using `[← QCoh.coe_appLinear, this]`. Conclude with `LinearEquiv.bijective _`.
-/
theorem isIso_theta_of_frames {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ IsFrame e) : IsIso (theta g F) := by
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

section Step

open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))

/- English proof (translation)
Introduce `_ hx` and use `F.le k (h hx)`.
-/
theorem le_chart {k : F.J} {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) : V ≤ (g ≫ π) ⁻¹ᵁ (F.M k).U :=
  fun _ hx => F.le k (h hx)

def vecSec (k : F.J) (V : C.Opens) (h : V ≤ g ⁻¹ᵁ F.U k) (i : Fin (Dw.mult σ)) :
    Γ((Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G), V) :=
  ∑ a, g.appLE (F.U k) V h (F.u k σ a i) • pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a)

/- English proof (translation)
Rewrite using `[vecSec, vecSec, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Twist.resM_smul, DualPull.resG_appLE]`. Conclude with `congrArg _ (QCoh.res_pullbackSections _ _ _ _ _)`.
-/
theorem resM_vecSec (k : F.J) {V V' : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V' ≤ V) (i : Fin (Dw.mult σ)) :
    resM _ h' (vecSec F g σ f k V h i) = vecSec F g σ f k V' (h'.trans h) i := by
  rw [vecSec, vecSec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Twist.resM_smul, DualPull.resG_appLE]
  exact congrArg _ (QCoh.res_pullbackSections _ _ _ _ _)

/- English proof (translation)
Use `Y.t.semi` as an intermediate fact. Use `Y.t.semi.smooth` as an intermediate fact. Establish `: (Lie Y.t.G).IsQuasicoherent` using `OmegaGlobal.isQuasicoherent_of_frames fun x =>`. Establish `⟨U, n, _, hx, he⟩` using `exists_isFrame_omega Y.t.G x`. Use the proof step `⟨U, n, _, hx, he.dual⟩`.

Set `b` to `((hf (F.M k).toMChart).pullback (g ≫ π)).basis (le_chart F g h)`. Establish `hb : ∀ a, b a = pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a)` using `fun a => (IsFrame.basis_apply _ _ a).trans (QCoh.res_pullbackSections _ _ _ _ _)`. Take `⟨w, hw⟩` from `F.split k σ`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`.

Simplify using `only [vecSec, ← hb, Finset.smul_sum, smul_smul] at ha`. Rewrite `ha` using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul] at ha`. Establish `h₁ : ((F.u k σ).map (g.appLE (F.U k) V h).hom).mulVec a = 0` using `funext fun j => show ∑ i, g.appLE (F.U k) V h (F.u k σ j i) * a i = 0 from Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _) (Fintype.linearIndependent_iff.1 b.linearIndependent _ ha j)`. Establish `h₂` using `congrArg (w.map (g.appLE (F.U k) V h).hom).mulVec h₁`.

Rewrite `h₂` using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Matrix.mulVec_zero]`. Conclude with `congrFun h₂`.
-/
theorem linearIndependent_vecSec (hf : ∀ M, IsFrame (f M)) (k : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) :
    LinearIndependent Γ(C, V) (vecSec F g σ f k V h) := by
  have := Y.t.semi
  have := Y.t.semi.smooth
  have : (Lie Y.t.G).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := exists_isFrame_omega Y.t.G x
    ⟨U, n, _, hx, he.dual⟩
  let b := ((hf (F.M k).toMChart).pullback (g ≫ π)).basis (le_chart F g h)
  have hb : ∀ a, b a = pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a) := fun a =>
    (IsFrame.basis_apply _ _ a).trans (QCoh.res_pullbackSections _ _ _ _ _)
  obtain ⟨w, hw⟩ := F.split k σ
  rw [Fintype.linearIndependent_iff]
  intro a ha
  simp only [vecSec, ← hb, Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simp only [← Finset.sum_smul] at ha
  have h₁ : ((F.u k σ).map (g.appLE (F.U k) V h).hom).mulVec a = 0 := funext fun j =>
    show ∑ i, g.appLE (F.U k) V h (F.u k σ j i) * a i = 0 from
    Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _)
      (Fintype.linearIndependent_iff.1 b.linearIndependent _ ha j)
  have h₂ := congrArg (w.map (g.appLE (F.U k) V h).hom).mulVec h₁
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
    Matrix.mulVec_zero] at h₂
  exact congrFun h₂

/- English proof (translation)
Establish `hM : V ≤ (g ≫ π) ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U)` using `fun _ hx => ⟨le_chart F g h hx, le_chart F g h' hx⟩`. Establish `e₁ : ∀ a, pullbackSections (g ≫ π) _ (le_chart F g h') (f (F.M k').toMChart a) = ∑ b, (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) • pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart b)` using `fun a => by`. Use `congrArg (pullbackSections (g ≫ π) _ hM) (hc (F.M k).toMChart (F.M k').toMChart a)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Use `((QCoh.pullbackSections_res _ _ _ _ _).symm.trans this).trans (Finset.sum_congr rfl fun b _ => ?_)` and prove the remaining obligations.

Rewrite using `[QCoh.pullbackSections_smul]`. Conclude with `congrArg _ (QCoh.pullbackSections_res _ _ _ _ _)`. Establish `e₂ : ∀ b, ∑ a, g.appLE _ V h' (F.u k' σ a i) * (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) = ∑ j, g.appLE _ V hh (F.B k k' σ j i) * g.appLE _ V h (F.u k σ b j)` using `fun b => by`. Establish `e₀ : ∑ a, π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k')) (chg (F.M k).toMChart (F.M k').toMChart b a) * resG Z inf_le_right (F.u k' σ a i) = ∑ j, resG Z inf_le_left (F.u k σ b j) * F.B k k' σ j i` using `congrFun (congrFun (F.tri k k' σ).choose_spec.2 b) i`. Use `congrArg (g.appLE _ V hh).hom e₀` as an intermediate fact.

Rewrite `this` using `[map_sum, map_sum]`. Use `(Finset.sum_congr rfl fun a _ => ?_).trans (this.trans (Finset.sum_congr rfl fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[_root_.mul_comm, map_mul, ← Scheme.Hom.appLE_comp_appLE g π _ _ V (inf_le_inf (F.le k) (F.le k')) hh]`. Conclude with `congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _).symm`. Rewrite using `[map_mul, _root_.mul_comm]`.

Conclude with `congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _)`. Simplify using `only [vecSec, e₁, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin (Dw.mult σ))))]`. Simplify using `only [← Finset.sum_smul, e₂]`.
-/
theorem vecSec_chg (hc : ∀ (M M' : MChart Y) (j : Fin M'.n), resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) =
      ∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i))
    (k k' : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V ≤ g ⁻¹ᵁ F.U k') (hh : V ≤ g ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (i : Fin (Dw.mult σ)) : vecSec F g σ f k' V h' i =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) • vecSec F g σ f k V h j := by
  have hM : V ≤ (g ≫ π) ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U) := fun _ hx => ⟨le_chart F g h hx, le_chart F g h' hx⟩
  have e₁ : ∀ a, pullbackSections (g ≫ π) _ (le_chart F g h') (f (F.M k').toMChart a) =
      ∑ b, (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) •
        pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart b) := fun a => by
    have := congrArg (pullbackSections (g ≫ π) _ hM) (hc (F.M k).toMChart (F.M k').toMChart a)
    rw [map_sum] at this
    refine ((QCoh.pullbackSections_res _ _ _ _ _).symm.trans this).trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [QCoh.pullbackSections_smul]
    exact congrArg _ (QCoh.pullbackSections_res _ _ _ _ _)
  have e₂ : ∀ b, ∑ a, g.appLE _ V h' (F.u k' σ a i) *
      (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) * g.appLE _ V h (F.u k σ b j) := fun b => by
    have e₀ : ∑ a, π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))
        (chg (F.M k).toMChart (F.M k').toMChart b a) * resG Z inf_le_right (F.u k' σ a i) =
        ∑ j, resG Z inf_le_left (F.u k σ b j) * F.B k k' σ j i :=
      congrFun (congrFun (F.tri k k' σ).choose_spec.2 b) i
    have := congrArg (g.appLE _ V hh).hom e₀
    rw [map_sum, map_sum] at this
    refine (Finset.sum_congr rfl fun a _ => ?_).trans (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [_root_.mul_comm, map_mul, ← Scheme.Hom.appLE_comp_appLE g π _ _ V (inf_le_inf (F.le k) (F.le k')) hh]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _).symm
    · rw [map_mul, _root_.mul_comm]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _)
  simp only [vecSec, e₁, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin (Dw.mult σ))))]
  simp only [← Finset.sum_smul, e₂]

open Classical in

/- English proof (translation)
Establish `ht : ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id` using `fun a b h => F.B_tri k k' σ (show Fin.castLE hj b < Fin.castLE hj a from h)`. Rewrite using `[Matrix.det_of_upperTriangular ht]`. Express the relevant statement in the definitionally equal form `((∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹).val = _`. Establish `e : (∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹ = ∏ i : Fin j, F.T k k' (some ⟨σ, Fin.castLE hj i⟩)`. Rewrite using `[← Finset.prod_inv_distrib]`.

Use `(Finset.prod_of_injOn (fun i : Fin j => (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw)) (fun a _ b _ h => ?_) (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun i _ => ?_).symm` and prove the remaining obligations. Conclude with `Fin.castLE_injective hj (eq_of_heq (Sigma.mk.inj (Option.some.inj h)).2)`. Establish `: NefStep.stepEx σ j ix = 0`. Break down `ix with _ | ⟨σ', i⟩` into its components or cases. Both sides reduce to the same expression.

Use `if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨rfl, hi⟩`. Conclude with `h ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩`. Rewrite using `[this, neg_zero, zpow_zero, inv_one]`. Establish `: NefStep.stepEx σ j (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw) = 1` using `if_pos ⟨rfl, i.2⟩`.

Rewrite using `[this, zpow_neg_one, inv_inv]`. Rewrite using `[e, Units.coe_prod]`. Both sides reduce to the same expression.
-/
theorem val_dual_LL_stepEx {j : ℕ} (hj : j ≤ Dw.mult σ) (k k' : F.J) :
    ((CechPic.dual (F.LL (NefStep.stepEx σ j))).g k k').val =
      ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  have ht : ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := fun a b h =>
    F.B_tri k k' σ (show Fin.castLE hj b < Fin.castLE hj a from h)
  rw [Matrix.det_of_upperTriangular ht]
  change ((∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹).val = _
  have e : (∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹ = ∏ i : Fin j, F.T k k' (some ⟨σ, Fin.castLE hj i⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun i : Fin j => (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun i _ => ?_).symm
    · exact Fin.castLE_injective hj (eq_of_heq (Sigma.mk.inj (Option.some.inj h)).2)
    · have : NefStep.stepEx σ j ix = 0 := by
        rcases ix with _ | ⟨σ', i⟩
        · rfl
        · refine if_neg ?_
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
      rw [this, neg_zero, zpow_zero, inv_one]
    · have : NefStep.stepEx σ j (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw) = 1 := if_pos ⟨rfl, i.2⟩
      rw [this, zpow_neg_one, inv_inv]
  rw [e, Units.coe_prod]
  rfl

/- English proof (translation)
Take `⟨f, hf, hc⟩` from `GlobalTheory.T.exists_lieBundle_frames_charts_change_basis E H Dw l Xo c O β Y`. Use `GlobalTheory.T.exists_locallyFree_subsheaf_det_iso C _ j _ (isLB_chartwise (isLB_dual (F.isLB_LL _)) g).1 (fun k i => vecSec F g σ f k (g ⁻¹ᵁ F.U k) le_rfl (Fin.castLE hj i)) (fun k k' => ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (g.app (F.U k ⊓ F.U k')).hom) ( …` and prove the remaining obligations. Use `(linearIndependent_vecSec F g σ f hf k h).comp _ (Fin.castLE_injective hj)` as an intermediate fact. Conclude with `(funext fun i => resM_vecSec F g σ f k le_rfl h (Fin.castLE hj i)) ▸ this`. Use `(resM_vecSec F g σ f k' le_rfl _ _).trans ((vecSec_chg F g σ f hc k k' (V := g ⁻¹ᵁ F.U k ⊓ g ⁻¹ᵁ F.U k') inf_le_left inf_le_right le_rfl _).trans ?_)` and prove the remaining obligations.

Use `(Finset.sum_of_injOn (Fin.castLE hj) (Fin.castLE_injective hj).injOn (fun _ _ => Finset.mem_univ _) (fun a _ h => ?_) fun a _ => ?_).symm` and prove the remaining obligations. Establish `: F.B k k' σ a (Fin.castLE hj i) = 0` using `F.B_tri k k' σ (by`. Assume the negation of the conclusion as `h'`. Conclude with `h ⟨⟨a, lt_of_le_of_lt (not_lt.1 h') i.2⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)`. Rewrite using `[this, map_zero, zero_smul]`.

Conclude with `congrArg₂ (· • ·) congr($(g.appLE_eq_app (U := F.U k ⊓ F.U k')) _).symm (resM_vecSec F g σ f k le_rfl _ _)`. Conclude with `(congrArg (g.app (F.U k ⊓ F.U k')).hom (val_dual_LL_stepEx F σ hj k k')).trans (RingHom.map_det _ _)`.
-/
theorem exists_step {j : ℕ} (hj : j ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (ι : W ⟶ (Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G)), Mono ι ∧ IsVB W j ∧
      LBIso (chartwise (CechPic.dual (F.LL (NefStep.stepEx σ j))) g) (det W j) := by
  obtain ⟨f, hf, hc⟩ := GlobalTheory.T.exists_lieBundle_frames_charts_change_basis E H Dw l Xo c O β Y
  refine GlobalTheory.T.exists_locallyFree_subsheaf_det_iso C _ j _ (isLB_chartwise (isLB_dual (F.isLB_LL _)) g).1
    (fun k i => vecSec F g σ f k (g ⁻¹ᵁ F.U k) le_rfl (Fin.castLE hj i))
    (fun k k' => ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (g.app (F.U k ⊓ F.U k')).hom)
    (fun k V h => ?_) (fun k k' i => ?_) fun k k' => ?_
  · have := (linearIndependent_vecSec F g σ f hf k h).comp _ (Fin.castLE_injective hj)
    exact (funext fun i => resM_vecSec F g σ f k le_rfl h (Fin.castLE hj i)) ▸ this
  · refine (resM_vecSec F g σ f k' le_rfl _ _).trans ((vecSec_chg F g σ f hc k k'
      (V := g ⁻¹ᵁ F.U k ⊓ g ⁻¹ᵁ F.U k') inf_le_left inf_le_right le_rfl _).trans ?_)
    refine (Finset.sum_of_injOn (Fin.castLE hj) (Fin.castLE_injective hj).injOn (fun _ _ => Finset.mem_univ _)
      (fun a _ h => ?_) fun a _ => ?_).symm
    · have : F.B k k' σ a (Fin.castLE hj i) = 0 := F.B_tri k k' σ (by
        by_contra h'
        exact h ⟨⟨a, lt_of_le_of_lt (not_lt.1 h') i.2⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      rw [this, map_zero, zero_smul]
    · exact congrArg₂ (· • ·) congr($(g.appLE_eq_app (U := F.U k ⊓ F.U k')) _).symm
        (resM_vecSec F g σ f k le_rfl _ _)
  · exact (congrArg (g.app (F.U k ⊓ F.U k')).hom (val_dual_LL_stepEx F σ hj k k')).trans (RingHom.map_det _ _)

open scoped CategoryTheory.Obj in

/- English proof (translation)
Introduce `C _ hs hp hc g`. Take `⟨W, ι, _, hW, e⟩` from `exists_step F g σ hj`. Use `Y.t.semi` as an intermediate fact. Use `Y.t.semi.smooth` as an intermediate fact. Use `IsSemiAbelian.pullback (g ≫ π) Y.t.G Y.t.semi` as an intermediate fact.

Establish `hG` using `isGrpPullback_pullback Y.t.G (g ≫ π)`. Use `isIso_theta_of_frames (g ≫ π) (exists_isFrame_omega Y.t.G)` as an intermediate fact. Establish `: IsIso (lieBase hG)` using `inferInstanceAs (IsIso (DualPull.theta _ (omega Y.t.G) ≫ (dualIso (asIso (omegaBase hG)).symm).hom))`. Establish `hL` using `F.isLB_LL (NefStep.stepEx σ j)`. Establish `h₁` using `isLB_chartwise (isLB_dual hL) g`.

Use `(hS.dual_det_nonneg hs hp hc _ hW (ι ≫ lieBase hG)).trans_eq (interNum_congr_cls K _ (isLB_vecOne (isLB_dual hW.isLB_det)) (isLB_vecOne (LB.isLB_pull hL g)) fun i => ?_)` and prove the remaining obligations. Use `fin_cases i`. Express the relevant statement in the definitionally equal form `cls (CechPic.dual (det W j)) (isLB_dual hW.isLB_det) = cls ((F.LL (NefStep.stepEx σ j)).pull g) (LB.isLB_pull hL g)`. Rewrite using `[cls_dual hW.isLB_det, ← (cls_eq_iff h₁.1 hW.isLB_det).2 e, (cls_eq_iff h₁.1 (LB.isLB_pull (isLB_dual hL) g)).2 h₁.2, cls_pull (isLB_dual hL), cls_dual hL, map_neg, neg_neg, cls_pull hL]`.
-/
theorem curveTest_stepEx (hS : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] {j : ℕ}
    (hj : j ≤ Dw.mult σ) : NefCurveTest.CurveTest K (F.LL (NefStep.stepEx σ j)) := by
  intro C _ hs hp hc g
  obtain ⟨W, ι, _, hW, e⟩ := exists_step F g σ hj
  have := Y.t.semi
  have := Y.t.semi.smooth
  have := IsSemiAbelian.pullback (g ≫ π) Y.t.G Y.t.semi
  have hG := isGrpPullback_pullback Y.t.G (g ≫ π)
  have := isIso_theta_of_frames (g ≫ π) (exists_isFrame_omega Y.t.G)
  have : IsIso (lieBase hG) :=
    inferInstanceAs (IsIso (DualPull.theta _ (omega Y.t.G) ≫ (dualIso (asIso (omegaBase hG)).symm).hom))
  have hL := F.isLB_LL (NefStep.stepEx σ j)
  have h₁ := isLB_chartwise (isLB_dual hL) g
  refine (hS.dual_det_nonneg hs hp hc _ hW (ι ≫ lieBase hG)).trans_eq (interNum_congr_cls K _
    (isLB_vecOne (isLB_dual hW.isLB_det)) (isLB_vecOne (LB.isLB_pull hL g)) fun i => ?_)
  fin_cases i
  change cls (CechPic.dual (det W j)) (isLB_dual hW.isLB_det) =
    cls ((F.LL (NefStep.stepEx σ j)).pull g) (LB.isLB_pull hL g)
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff h₁.1 hW.isLB_det).2 e,
    (cls_eq_iff h₁.1 (LB.isLB_pull (isLB_dual hL) g)).2 h₁.2, cls_pull (isLB_dual hL), cls_dual hL, map_neg, neg_neg,
    cls_pull hL]

end Step

/- English proof (translation)
The claim follows from `letI := algebraΓOfHom (str₀ X Z) ((curveTest_stepEx X.F σ hS _ hj).pull (X.F.isLB_LL _) _).isNef hN (LB.isLB_pull (X.F.isLB_LL _) _)`.
-/
theorem isNef_stepEx (hS : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) {E : Type} [Field E]
    [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y) (Z : Comp Xo c) (σ : E →+* ℂ) {j : ℕ}
    (hj : j ≤ Dw.mult σ) : letI := algebraΓOfHom (str₀ X Z); IsNef c.F (LL₀ X Z (NefStep.stepEx σ j)) :=
  letI := algebraΓOfHom (str₀ X Z)
  ((curveTest_stepEx X.F σ hS _ hj).pull (X.F.isLB_LL _) _).isNef hN (LB.isLB_pull (X.F.isLB_LL _) _)

/- English proof (translation)
Introduce `hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk`. Rewrite using `[NefStep.L₀_headWt TF.X Z τ k hk]`. Conclude with `isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)`.
-/
theorem isNef_headWt : GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  intro hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk
  rw [NefStep.L₀_headWt TF.X Z τ k hk]
  exact isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)

end GlobalTheory.NefHodge
