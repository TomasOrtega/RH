import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationFlagFiltrationExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMapExtendsAfterScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairDivisorClassSumStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.FlagRankTwoStar

open GlobalTheory.Vert.Model
open GlobalTheory.VB (IsVB Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)
open GlobalTheory.LB (resG_resG resG_self)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : Model O}

/- English proof (translation)
Set `s : (φ.div hE hE').M.Sec` to `⟨fun p : Chart E 1 × Chart E' 1 => (p.1.isFrame.basis (inf_le_left : p.1.U ⊓ p.2.U ≤ _)).det fun i => j.app _ (resM E' inf_le_right (p.2.e i)), fun p q => Z.resG_injective inf_le_right le_rfl <| by`. Express the relevant statement in the definitionally equal form `resG _ _ (resG _ _ _) = resG _ _ (_ * resG _ _ _)`. Rewrite using `[map_mul, resG_resG, resG_resG]`. Conclude with `(GenIso.eqn_div_of_hom hE hE' hj p.1 p.2 (inf_le_inf_left _ inf_le_left) le_rfl).symm.trans (((φ.div hE hE').eqn_rel p q _ _ _).trans (congrArg _ (GenIso.eqn_div_of_hom hE hE' hj q.1 q.2 (inf_le_inf_left _ inf_le_right) le_rfl)))⟩`. Establish `h : (φ.div hE hE').Extends 1 s` using `VertDiv.extends_one (LB.sec_ext fun p => (GenIso.eqn_div_of_hom hE hE' hj p.1 p.2 le_rfl le_rfl).symm.trans (resG_self _ _))`.

Use `⟨h.eff one_ne_zero, h.cls_eq_ofEff.symm, ?_⟩` and prove the remaining obligations. Establish `hN` using `hE.isLB_det`. Establish `hM` using `Twist.isLB_lbZPow hN (-1)`. Take `⟨e₁⟩` from `nonempty_twist_twist_iso_of_cls_eq (structureModule Z.X) hN hM (LB.isLB_triv _) (by rw [cls_lbZPow hN, neg_one_zsmul, add_neg_cancel]; rfl)`. Set `e : twist E (lbZPow (det E 1) (-1)) ≅ structureModule Z.X` to `(twistFunctor _).mapIso (hE.isoDet ≪≫ (Twist.unitTwistIso _).symm) ≪≫ e₁ ≪≫ (Twist.trivIso _).symm`.

Use `Twist.preservesFiniteColimits_twistFunctor hM` as an intermediate fact. Use `hE'.isQuasicoherent` as an intermediate fact. Use `Twist.isQuasicoherent_twist (F := E') hM` as an intermediate fact. Establish `H : IsMulBy (Twist.map (lbZPow (det E 1) (-1)) j ≫ e.hom) (EffCartierData.ofSec (φ.div hE hE').isLB s (h.isRegularSec one_ne_zero)).canonical`. Introduce and unpack `⟨c, c'⟩ V hV`.

Establish `h₁ : V ≤ c.U` using `hV.trans inf_le_left`. Establish `h₂ : V ≤ c'.U` using `hV.trans inf_le_right`. Set `u : Γ(E', V) ≃ₗ[Γ(Z.X, V)] Γ(E, V)` to `(c'.isFrame.basis h₂).equiv (c.isFrame.basis h₁) (Equiv.refl _)`. Establish `hu (t : Γ(E', V)) : j.app V t = resG Z.X hV (s.f (c, c')) • u t`. Establish `: appLinear j V = resG Z.X hV (s.f (c, c')) • u.toLinearMap` using `(c'.isFrame.basis h₂).ext fun i => by`.

Take `rfl : i = 0` from `Subsingleton.elim _ _`. Establish `e₂ : resG Z.X hV (s.f (c, c')) = (c.isFrame.basis h₁).repr (j.app V (c'.isFrame.basis h₂ 0)) 0`. Use `(c.isFrame.resG_det _ hV _).trans ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply, VB.IsFrame.basis_apply]`. Use `congrArg (fun t => (c.isFrame.basis h₁).repr t 0) ?_` and prove the remaining obligations.

Conclude with `(app_resM j hV _).symm.trans (congrArg (j.app V) (resM_resM _ _ _))`. Rewrite using `[e₂, LinearMap.smul_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, appLinear_apply]`. Use `conv_lhs => rw [← (c.isFrame.basis h₁).sum_repr (j.app V _), Fin.sum_univ_one]`. Conclude with `LinearMap.congr_fun this t`. Use `⟨Twist.zchartEquiv hN (-1) c h₁ ≪≫ₗ u ≪≫ₗ (Twist.zchartEquiv hN (-1) c h₁).symm ≪≫ₗ LinearEquiv.ofBijective (appLinear e.hom V) (ConcreteCategory.bijective_of_isIso (e.hom.app V)), fun t => ?_⟩` and prove the remaining obligations.

Establish `e₃ : (Twist.map (lbZPow (det E 1) (-1)) j).app V t = resG Z.X hV (s.f (c, c')) • (Twist.zchartEquiv hN (-1) c h₁).symm (u (Twist.zchartEquiv hN (-1) c h₁ t))`. Use `(Twist.zchartEquiv hN (-1) c h₁).injective ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, ← hu]`. Conclude with `Twist.chartEquiv_map_app hM _ _ _ t`. Express the relevant statement in the definitionally equal form `e.hom.app V ((Twist.map (lbZPow (det E 1) (-1)) j).app V t) = _`.

Rewrite using `[e₃]`. Conclude with `map_smul (appLinear e.hom V) _ _`. Take `⟨k⟩` from `nonempty_cokernel_iso _ H`. Conclude with `⟨PreservesCokernel.iso (twistFunctor _) j ≪≫ (cokernelCompIsIso _ e.hom).symm ≪≫ k⟩`.
-/
theorem exists_cokernel_twist_iso {E E' : Z.X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1)
    {φ : Z.GenIso E E'} {j : E' ⟶ E} (hj : φ.inv = Z.genRes.map j) :
    ∃ I : Z.effVert, ofEff I = (φ.div hE hE').cls ∧
      Nonempty (twist (cokernel j) (lbZPow (det E 1) (-1)) ≅ divMod I.1) := by
  let s : (φ.div hE hE').M.Sec :=
    ⟨fun p : Chart E 1 × Chart E' 1 => (p.1.isFrame.basis (inf_le_left : p.1.U ⊓ p.2.U ≤ _)).det
      fun i => j.app _ (resM E' inf_le_right (p.2.e i)), fun p q =>
      Z.resG_injective inf_le_right le_rfl <| by
        change resG _ _ (resG _ _ _) = resG _ _ (_ * resG _ _ _)
        rw [map_mul, resG_resG, resG_resG]
        exact (GenIso.eqn_div_of_hom hE hE' hj p.1 p.2 (inf_le_inf_left _ inf_le_left)
          le_rfl).symm.trans (((φ.div hE hE').eqn_rel p q _ _ _).trans (congrArg _
            (GenIso.eqn_div_of_hom hE hE' hj q.1 q.2 (inf_le_inf_left _ inf_le_right) le_rfl)))⟩
  have h : (φ.div hE hE').Extends 1 s := VertDiv.extends_one (LB.sec_ext fun p =>
    (GenIso.eqn_div_of_hom hE hE' hj p.1 p.2 le_rfl le_rfl).symm.trans (resG_self _ _))
  refine ⟨h.eff one_ne_zero, h.cls_eq_ofEff.symm, ?_⟩
  have hN := hE.isLB_det
  have hM := Twist.isLB_lbZPow hN (-1)
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule Z.X) hN hM (LB.isLB_triv _)
    (by rw [cls_lbZPow hN, neg_one_zsmul, add_neg_cancel]; rfl)
  let e : twist E (lbZPow (det E 1) (-1)) ≅ structureModule Z.X :=
    (twistFunctor _).mapIso (hE.isoDet ≪≫ (Twist.unitTwistIso _).symm) ≪≫ e₁ ≪≫
      (Twist.trivIso _).symm
  have := Twist.preservesFiniteColimits_twistFunctor hM
  have := hE'.isQuasicoherent
  have := Twist.isQuasicoherent_twist (F := E') hM
  have H : IsMulBy (Twist.map (lbZPow (det E 1) (-1)) j ≫ e.hom)
      (EffCartierData.ofSec (φ.div hE hE').isLB s (h.isRegularSec one_ne_zero)).canonical := by
    rintro ⟨c, c'⟩ V hV
    have h₁ : V ≤ c.U := hV.trans inf_le_left
    have h₂ : V ≤ c'.U := hV.trans inf_le_right
    let u : Γ(E', V) ≃ₗ[Γ(Z.X, V)] Γ(E, V) :=
      (c'.isFrame.basis h₂).equiv (c.isFrame.basis h₁) (Equiv.refl _)
    have hu (t : Γ(E', V)) : j.app V t = resG Z.X hV (s.f (c, c')) • u t := by
      have : appLinear j V = resG Z.X hV (s.f (c, c')) • u.toLinearMap :=
        (c'.isFrame.basis h₂).ext fun i => by
          obtain rfl : i = 0 := Subsingleton.elim _ _
          have e₂ : resG Z.X hV (s.f (c, c')) =
              (c.isFrame.basis h₁).repr (j.app V (c'.isFrame.basis h₂ 0)) 0 := by
            refine (c.isFrame.resG_det _ hV _).trans ?_
            rw [Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
              VB.IsFrame.basis_apply]
            refine congrArg (fun t => (c.isFrame.basis h₁).repr t 0) ?_
            exact (app_resM j hV _).symm.trans (congrArg (j.app V) (resM_resM _ _ _))
          rw [e₂, LinearMap.smul_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
            Equiv.refl_apply, appLinear_apply]
          conv_lhs => rw [← (c.isFrame.basis h₁).sum_repr (j.app V _), Fin.sum_univ_one]
      exact LinearMap.congr_fun this t
    refine ⟨Twist.zchartEquiv hN (-1) c h₁ ≪≫ₗ u ≪≫ₗ (Twist.zchartEquiv hN (-1) c h₁).symm ≪≫ₗ
      LinearEquiv.ofBijective (appLinear e.hom V)
        (ConcreteCategory.bijective_of_isIso (e.hom.app V)), fun t => ?_⟩
    have e₃ : (Twist.map (lbZPow (det E 1) (-1)) j).app V t = resG Z.X hV (s.f (c, c')) •
        (Twist.zchartEquiv hN (-1) c h₁).symm (u (Twist.zchartEquiv hN (-1) c h₁ t)) := by
      refine (Twist.zchartEquiv hN (-1) c h₁).injective ?_
      rw [map_smul, LinearEquiv.apply_symm_apply, ← hu]
      exact Twist.chartEquiv_map_app hM _ _ _ t
    change e.hom.app V ((Twist.map (lbZPow (det E 1) (-1)) j).app V t) = _
    rw [e₃]
    exact map_smul (appLinear e.hom V) _ _
  obtain ⟨k⟩ := nonempty_cokernel_iso _ H
  exact ⟨PreservesCokernel.iso (twistFunctor _) j ≪≫ (cokernelCompIsIso _ e.hom).symm ≪≫ k⟩

/- English proof (translation)
Take `⟨I, hI, ⟨e⟩⟩` from `exists_cokernel_twist_iso hE hE' hj`. Establish `hN` using `hE.isLB_det`. Establish `hM` using `Twist.isLB_lbZPow hN (-1)`. Take `⟨e₁⟩` from `nonempty_twist_twist_iso_of_cls_eq (cokernel j) hM hN (LB.isLB_triv _) (by rw [cls_lbZPow hN, neg_one_zsmul, neg_add_cancel]; rfl)`. Set `k : twist (divMod I.1) (det E 1) ≅ cokernel j` to `(twistFunctor _).mapIso e.symm ≪≫ e₁ ≪≫ (Twist.trivIso _).symm`.

Conclude with `⟨I, hI, ((isVertical_divMod I).finiteLenTwists.twist hN).of_iso k, fun x => by`. Rewrite using `[← chiLenPic_congr O k, chiLenPic_twist O _ hN]⟩`.
-/
theorem exists_chi_cokernel {E E' : Z.X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1)
    {φ : Z.GenIso E E'} {j : E' ⟶ E} (hj : φ.inv = Z.genRes.map j) :
    ∃ I : Z.effVert, ofEff I = (φ.div hE hE').cls ∧ FiniteLenTwists O (cokernel j) ∧
      ∀ x, chiLenPic O (cokernel j) x = chiLenPic O (divMod I.1) (cls _ hE.isLB_det + x) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_cokernel_twist_iso hE hE' hj
  have hN := hE.isLB_det
  have hM := Twist.isLB_lbZPow hN (-1)
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq (cokernel j) hM hN (LB.isLB_triv _)
    (by rw [cls_lbZPow hN, neg_one_zsmul, neg_add_cancel]; rfl)
  let k : twist (divMod I.1) (det E 1) ≅ cokernel j :=
    (twistFunctor _).mapIso e.symm ≪≫ e₁ ≪≫ (Twist.trivIso _).symm
  exact ⟨I, hI, ((isVertical_divMod I).finiteLenTwists.twist hN).of_iso k, fun x => by
    rw [← chiLenPic_congr O k, chiLenPic_twist O _ hN]⟩

/- English proof (translation)
Take `⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩` from `h`. Establish `k₁` using `h₁.of_iso e₁.symm`. Establish `k₃` using `h₃.of_iso e₃.symm`. Use `⟨FiniteLenTwists.of_iso (fun M hM => FiniteLenCoh.of_shortExact₂ (Twist.shortExact_map hM hS) (k₁ M hM) (k₃ M hM)) e₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← chiLenPic_congr O e₁, ← chiLenPic_congr O e₂, ← chiLenPic_congr O e₃]`.

Conclude with `chiLenPic_shortExact hS k₁ k₃`.
-/
theorem chi_of_isExt {F₁ F₂ F₃ : Z.X.Modules} (h : IsExt F₁ F₂ F₃) (h₁ : FiniteLenTwists O F₁)
    (h₃ : FiniteLenTwists O F₃) :
    FiniteLenTwists O F₂ ∧ chiLenPic O F₂ = chiLenPic O F₁ + chiLenPic O F₃ := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := h
  have k₁ := h₁.of_iso e₁.symm
  have k₃ := h₃.of_iso e₃.symm
  refine ⟨FiniteLenTwists.of_iso (fun M hM => FiniteLenCoh.of_shortExact₂
    (Twist.shortExact_map hM hS) (k₁ M hM) (k₃ M hM)) e₂, ?_⟩
  rw [← chiLenPic_congr O e₁, ← chiLenPic_congr O e₂, ← chiLenPic_congr O e₃]
  exact chiLenPic_shortExact hS k₁ k₃

/- English proof (translation)
Introduce `_ hM` and use `have k n := cohOn.subsingleton_of_isZero ((Twist.isZero_twist_iff hM).2 h) ⊤ n ⟨fun n => by have := k n; simp [Module.length_eq_zero], 0, fun n _ => k n⟩`.
-/
theorem finiteLenTwists_of_isZero {F : Z.X.Modules} (h : IsZero F) : FiniteLenTwists O F :=
  fun _ hM =>
    have k n := cohOn.subsingleton_of_isZero ((Twist.isZero_twist_iff hM).2 h) ⊤ n
    ⟨fun n => by have := k n; simp [Module.length_eq_zero], 0, fun n _ => k n⟩

/- English proof (translation)
Set `Q : Pres Z` to `⟨2, W, W', P.fl.isVB_self, P.fl'.isVB_self, u, hu⟩`. Establish `: IsIso (Z.genRes.map Q.ψ)` using `hu`. Take `⟨I, hI, fI, cI⟩` from `exists_chi_cokernel (P.fl.isVB_gr 0) (P.fl'.isVB_gr 0) (FlagFilt.genRes_grψ (P := Q) P (0 : Fin 2)).symm`. Take `⟨J, hJ, fJ, cJ⟩` from `exists_chi_cokernel (P.fl.isVB_gr 1) (P.fl'.isVB_gr 1) (FlagFilt.genRes_grψ (P := Q) P (1 : Fin 2)).symm`. Establish `z` using `FlagFilt.isZero_stepPres_zero (P := Q) P`.

Take `⟨f₁, c₁⟩` from `chi_of_isExt (FlagFilt.isExt_step (P := Q) P (0 : Fin 2)) (finiteLenTwists_of_isZero z) fI`. Take `⟨-, c₂⟩` from `chi_of_isExt (FlagFilt.isExt_step (P := Q) P (1 : Fin 2)) f₁ fJ`. Use `⟨I, J, hI, hJ, fun x => ?_⟩` and prove the remaining obligations. Establish `e` using `chiLenPic_congr O (FlagFilt.stepPresLastIso (P := Q) P)`. Establish `c₀` using `congrFun (chiLenPic_eq_zero_of_isZero O z) x`.

Conclude with `(congrFun e x).symm.trans ((congrFun c₂ x).trans (congrArg₂ (· + ·) ((congrFun c₁ x).trans ((congrArg₂ (· + ·) c₀ (cI x)).trans (zero_add _))) (cJ x)))`.
-/
theorem exists_chi_rank_two {W W' : Z.X.Modules} (u : W' ⟶ W) [hu : IsIso (Z.genRes.map u)]
    (P : FlagPair (GenIso.ofHom u) 2) : ∃ I J : Z.effVert, ofEff I = (P.div 0).cls ∧
      ofEff J = (P.div 1).cls ∧ ∀ x, chiLenPic O (cokernel u) x =
        chiLenPic O (divMod I.1) (cls _ (P.fl.isLB_root 0) + x) +
          chiLenPic O (divMod J.1) (cls _ (P.fl.isLB_root 1) + x) := by
  let Q : Pres Z := ⟨2, W, W', P.fl.isVB_self, P.fl'.isVB_self, u, hu⟩
  have : IsIso (Z.genRes.map Q.ψ) := hu
  obtain ⟨I, hI, fI, cI⟩ := exists_chi_cokernel (P.fl.isVB_gr 0) (P.fl'.isVB_gr 0)
    (FlagFilt.genRes_grψ (P := Q) P (0 : Fin 2)).symm
  obtain ⟨J, hJ, fJ, cJ⟩ := exists_chi_cokernel (P.fl.isVB_gr 1) (P.fl'.isVB_gr 1)
    (FlagFilt.genRes_grψ (P := Q) P (1 : Fin 2)).symm
  have z := FlagFilt.isZero_stepPres_zero (P := Q) P
  obtain ⟨f₁, c₁⟩ := chi_of_isExt (FlagFilt.isExt_step (P := Q) P (0 : Fin 2))
    (finiteLenTwists_of_isZero z) fI
  obtain ⟨-, c₂⟩ := chi_of_isExt (FlagFilt.isExt_step (P := Q) P (1 : Fin 2)) f₁ fJ
  refine ⟨I, J, hI, hJ, fun x => ?_⟩
  have e := chiLenPic_congr O (FlagFilt.stepPresLastIso (P := Q) P)
  have c₀ := congrFun (chiLenPic_eq_zero_of_isZero O z) x
  exact (congrFun e x).symm.trans ((congrFun c₂ x).trans (congrArg₂ (· + ·)
    ((congrFun c₁ x).trans ((congrArg₂ (· + ·) c₀ (cI x)).trans (zero_add _))) (cJ x)))

/- English proof (translation)
Use `LinearMap.congr_fun (picSym_linearMap_ext (l := effDeg I₁ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₁) + effDeg I₂ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₂)) (l' := effDeg I₃ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₃) + effDeg I₄ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₄)) fun n g => …` and prove the remaining obligations. Establish `key (a : Pic Z.X) : firstChernPic a * ∏ i, firstChernPic (g i) = ∏ i : Fin (n + 1), firstChernPic ((Fin.cons a g : Fin (n + 1) → Pic Z.X) i)`. Rewrite using `[Fin.prod_univ_succ]`. Both sides reduce to the same expression. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, key, effDeg, IsVertical.deg, picForm_prod]`.

Use `split_ifs with hn`. Establish `k (I : Z.effVert) (e t : Pic Z.X) : multiDiff (Fin.cons e g : Fin (n + 1) → Pic Z.X) (chiLenPic O (divMod I.1)) 0 = multiDiff g (fun x => bwdDiff e (chiLenPic O (divMod I.1)) (t + x)) 0`. Rewrite using `[multiDiff_translate, ← multiDiff_cons']`. Conclude with `(isVertical_divMod I).diffVanish.multiDiff_eq_of_le_card hn.ge _ _ _`. Rewrite using `[k I₁ e₁ t₁, k I₂ e₂ t₂, k I₃ e₃ t₃, k I₄ e₄ t₄, ← Int.cast_add, ← Int.cast_add, ← Pi.add_apply, ← Pi.add_apply (multiDiff g _), ← multiDiff_add, ← multiDiff_add]`.

Conclude with `congrArg (fun φ => ((multiDiff g φ 0 : ℤ) : ℚ)) (funext h)`. Both sides reduce to the same expression.
-/
theorem effDeg_add_eq {I₁ I₂ I₃ I₄ : Z.effVert} {e₁ e₂ e₃ e₄ t₁ t₂ t₃ t₄ : Pic Z.X}
    (h : ∀ x, bwdDiff e₁ (chiLenPic O (divMod I₁.1)) (t₁ + x) +
      bwdDiff e₂ (chiLenPic O (divMod I₂.1)) (t₂ + x) =
      bwdDiff e₃ (chiLenPic O (divMod I₃.1)) (t₃ + x) +
        bwdDiff e₄ (chiLenPic O (divMod I₄.1)) (t₄ + x)) (y : PicSym Z.X) :
    effDeg I₁ (firstChernPic e₁ * y) + effDeg I₂ (firstChernPic e₂ * y) =
      effDeg I₃ (firstChernPic e₃ * y) + effDeg I₄ (firstChernPic e₄ * y) := by
  refine LinearMap.congr_fun (picSym_linearMap_ext
    (l := effDeg I₁ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₁) + effDeg I₂ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₂))
    (l' := effDeg I₃ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₃) + effDeg I₄ ∘ₗ LinearMap.mulLeft ℚ (firstChernPic e₄))
    fun n g => ?_) y
  have key (a : Pic Z.X) : firstChernPic a * ∏ i, firstChernPic (g i) =
      ∏ i : Fin (n + 1), firstChernPic ((Fin.cons a g : Fin (n + 1) → Pic Z.X) i) := by
    rw [Fin.prod_univ_succ]; rfl
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, key, effDeg,
    IsVertical.deg, picForm_prod]
  split_ifs with hn
  · have k (I : Z.effVert) (e t : Pic Z.X) :
        multiDiff (Fin.cons e g : Fin (n + 1) → Pic Z.X) (chiLenPic O (divMod I.1)) 0 =
          multiDiff g (fun x => bwdDiff e (chiLenPic O (divMod I.1)) (t + x)) 0 := by
      rw [multiDiff_translate, ← multiDiff_cons']
      exact (isVertical_divMod I).diffVanish.multiDiff_eq_of_le_card hn.ge _ _ _
    rw [k I₁ e₁ t₁, k I₂ e₂ t₂, k I₃ e₃ t₃, k I₄ e₄ t₄, ← Int.cast_add, ← Int.cast_add,
      ← Pi.add_apply, ← Pi.add_apply (multiDiff g _), ← multiDiff_add, ← multiDiff_add]
    exact congrArg (fun φ => ((multiDiff g φ 0 : ℤ) : ℚ)) (funext h)
  · rfl

/- English proof (translation)
Take `⟨a, c, ha, hc, h⟩` from `exists_chi_rank_two u P`. Take `⟨b, d, hb, hd, h'⟩` from `exists_chi_rank_two u P'`. Establish `hs : ofEff a + ofEff c = ofEff b + ofEff d`. Rewrite using `[ha, hb, hc, hd, GlobalTheory.T.flag_pair_divisor_class_sum O Z W W' _ P, GlobalTheory.T.flag_pair_divisor_class_sum O Z W W' _ P']`. Establish `hs' : a * c = b * d` using `ofEff_injective (by rw [ofEff_mul, ofEff_mul, hs])`.

Establish `hr` using `P.fl.cls_det.symm.trans P'.fl.cls_det`. Rewrite `hr` using `[Fin.sum_univ_two, Fin.sum_univ_two]`. Establish `r₁` using `P'.cls_root' 1`. Establish `r₀` using `P.cls_root' 0`. Rewrite `r₁` using `[← hd]`.

Rewrite `r₀` using `[← ha]`. Simplify using `only [← firstChernPic_class]`. Rewrite using `[r₁, r₀, ← ha, ← hb, ← hc]`. Generalize the expression as in `cls _ (P.fl.isLB_root 0) = l at *`. Generalize the expression as in `cls _ (P.fl.isLB_root 1) = n at *`.

Generalize the expression as in `cls _ (P'.fl.isLB_root 0) = m at *`. Generalize the expression as in `cls _ (P'.fl.isLB_root 1) = k at *`. Establish `E` using `effDeg_add_eq (I₁ := a) (I₂ := c) (I₃ := b) (I₄ := d) (e₁ := l + effCls c) (e₂ := n) (e₃ := m + effCls d) (e₄ := k) (t₁ := l) (t₂ := n) (t₃ := m) (t₄ := k) (fun x => by`. Establish `e₁` using `(h x).symm.trans (h' x)`. Establish `e₂` using `Check.chiLenPic_mul a c x`.

Establish `e₃` using `Check.chiLenPic_mul b d x`. Rewrite `e₂` using `[hs']`. Simplify using `only [bwdDiff_apply, add_sub_add_left_eq_sub, add_sub_cancel_left]`. Use the proof step `omega) y`. Simplify using `only [← vDeg_ofEff, ← vCls_ofEff] at E`.

Establish `S` using `Check.vDeg_symm (ofEff a) (ofEff b) y`. Take `rfl : k = l + n - m` from `by rw [hr]; abel`. Establish `hd' : ofEff d = ofEff a + ofEff c - ofEff b` using `by rw [hs]; abel`. Rewrite `E`, the goal using `[hd']`. Simplify using `only [map_add, map_sub, add_mul, sub_mul, LinearMap.add_apply, LinearMap.sub_apply] at E ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vDeg_rel_of_hom {W W' : Z.X.Modules} (u : W' ⟶ W) [IsIso (Z.genRes.map u)]
    (P P' : FlagPair (GenIso.ofHom u) 2) (y : PicSym Z.X) :
    Z.vDeg ((P.div 1).cls - (P'.div 0).cls)
        ((c1 (P.fl.root 0) (P.fl.isLB_root 0) - c1 (P'.fl.root 0) (P'.fl.isLB_root 0)) * y) +
      Z.vDeg ((P.div 0).cls - (P'.div 0).cls)
        ((c1 (P'.fl'.root 1) (P'.fl'.isLB_root 1) - c1 (P.fl'.root 0) (P.fl'.isLB_root 0)) * y) =
      0 := by
  obtain ⟨a, c, ha, hc, h⟩ := exists_chi_rank_two u P
  obtain ⟨b, d, hb, hd, h'⟩ := exists_chi_rank_two u P'
  have hs : ofEff a + ofEff c = ofEff b + ofEff d := by
    rw [ha, hb, hc, hd, GlobalTheory.T.flag_pair_divisor_class_sum O Z W W' _ P, GlobalTheory.T.flag_pair_divisor_class_sum O Z W W' _ P']
  have hs' : a * c = b * d := ofEff_injective (by rw [ofEff_mul, ofEff_mul, hs])
  have hr := P.fl.cls_det.symm.trans P'.fl.cls_det
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hr
  have r₁ := P'.cls_root' 1
  have r₀ := P.cls_root' 0
  rw [← hd] at r₁
  rw [← ha] at r₀
  simp only [← firstChernPic_class]
  rw [r₁, r₀, ← ha, ← hb, ← hc]
  generalize cls _ (P.fl.isLB_root 0) = l at *
  generalize cls _ (P.fl.isLB_root 1) = n at *
  generalize cls _ (P'.fl.isLB_root 0) = m at *
  generalize cls _ (P'.fl.isLB_root 1) = k at *
  have E := effDeg_add_eq (I₁ := a) (I₂ := c) (I₃ := b) (I₄ := d) (e₁ := l + effCls c) (e₂ := n)
    (e₃ := m + effCls d) (e₄ := k) (t₁ := l) (t₂ := n) (t₃ := m) (t₄ := k) (fun x => by
      have e₁ := (h x).symm.trans (h' x)
      have e₂ := Check.chiLenPic_mul a c x
      have e₃ := Check.chiLenPic_mul b d x
      rw [hs'] at e₂
      simp only [bwdDiff_apply, add_sub_add_left_eq_sub, add_sub_cancel_left]
      omega) y
  simp only [← vDeg_ofEff, ← vCls_ofEff] at E
  have S := Check.vDeg_symm (ofEff a) (ofEff b) y
  obtain rfl : k = l + n - m := by rw [hr]; abel
  have hd' : ofEff d = ofEff a + ofEff c - ofEff b := by rw [hs]; abel
  rw [hd'] at E ⊢
  simp only [map_add, map_sub, add_mul, sub_mul, LinearMap.add_apply, LinearMap.sub_apply] at E ⊢
  linarith

/- English proof (translation)
Set `S` to `FlagPair.ofSMul R.fl g hg`. Establish `e : GenIso.ofHom u = GenIso.smul W g hg ≪≫ ψ` using `Iso.ext ((Iso.inv_eq_inv _ _).1 hu)`. Set `P : FlagPair (GenIso.ofHom u) N` to `⟨R.fl, R.fl', fun i => S.gen i ≪≫ R.gen i, fun i => by`. Rewrite using `[Iso.trans_hom, Category.assoc, R.gen_ι, e, Iso.trans_hom, ← Category.assoc, ← Category.assoc]`. Conclude with `congrArg (· ≫ ψ.hom) (S.gen_ι i)⟩`.

Use `⟨P, rfl, rfl, fun i => ?_⟩` and prove the remaining obligations. Establish `k : P.grIso i = S.grIso i ≪≫ R.grIso i`. Use `Iso.ext ((cancel_epi (Z.genRes.map (R.fl.π i))).1 ?_)` and prove the remaining obligations. Conclude with `(P.π_grIso_hom i).trans ((Category.assoc _ _ _).trans ((congrArg ((S.gen i.succ).hom ≫ ·) (R.π_grIso_hom i).symm).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (R.grIso i).hom) (S.π_grIso_hom i).symm)).trans (Category.assoc _ _ _))))`. Rewrite using `[← FlagPair.cls_div_ofSMul R.fl g hg i]`.

Express the relevant statement in the definitionally equal form `((P.grIso i).div _ _).cls = _`. Rewrite using `[k]`. Conclude with `GenIso.cls_div_trans _ _ _ _ _`.
-/
theorem exists_flagPair_ofHom {W W' : Z.X.Modules} {ψ : Z.GenIso W W'} {N : ℕ} (R : FlagPair ψ N)
    {g : O} (hg : g ≠ 0) (u : W' ⟶ W) [IsIso (Z.genRes.map u)]
    (hu : Z.genRes.map u = ψ.inv ≫ Z.genRes.map (smulHom W (Z.const g))) :
    ∃ P : FlagPair (GenIso.ofHom u) N, P.fl = R.fl ∧ P.fl' = R.fl' ∧
      ∀ i, (P.div i).cls = Z.div g hg + (R.div i).cls := by
  let S := FlagPair.ofSMul R.fl g hg
  have e : GenIso.ofHom u = GenIso.smul W g hg ≪≫ ψ :=
    Iso.ext ((Iso.inv_eq_inv _ _).1 hu)
  let P : FlagPair (GenIso.ofHom u) N := ⟨R.fl, R.fl', fun i => S.gen i ≪≫ R.gen i, fun i => by
    rw [Iso.trans_hom, Category.assoc, R.gen_ι, e, Iso.trans_hom, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ ψ.hom) (S.gen_ι i)⟩
  refine ⟨P, rfl, rfl, fun i => ?_⟩
  have k : P.grIso i = S.grIso i ≪≫ R.grIso i := by
    refine Iso.ext ((cancel_epi (Z.genRes.map (R.fl.π i))).1 ?_)
    exact (P.π_grIso_hom i).trans ((Category.assoc _ _ _).trans
      ((congrArg ((S.gen i.succ).hom ≫ ·) (R.π_grIso_hom i).symm).trans
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (R.grIso i).hom)
          (S.π_grIso_hom i).symm)).trans (Category.assoc _ _ _))))
  rw [← FlagPair.cls_div_ofSMul R.fl g hg i]
  change ((P.grIso i).div _ _).cls = _
  rw [k]
  exact GenIso.cls_div_trans _ _ _ _ _

/- English proof (translation)
Introduce `O _ _ _ p _ _ _ B _ W W' ψ R R' y`. Take `⟨g, u, hg, hu⟩` from `GlobalTheory.ClearDenom.exists_smul_eq_genRes_map O B W' W _ _ R.fl'.isVB_self R.fl.isVB_self ψ.inv`. Use `isIso_genRes_map_smulHom W hg` as an intermediate fact. Establish `: IsIso (B.genRes.map u)` using `by rw [hu]; infer_instance`. Take `⟨P, h₁, h₂, hP⟩` from `exists_flagPair_ofHom R hg u hu`.

Take `⟨P', h₁', h₂', hP'⟩` from `exists_flagPair_ofHom R' hg u hu`. Establish `h` using `vDeg_rel_of_hom u P P' y`. Rewrite `h` using `[hP, hP, hP', add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, h₁, h₂, h₁', h₂']`. Rewrite using `[← map_sub, ← map_sub, capDeg_vp_toQ, capDeg_vp_toQ, ← add_div, h, zero_div]`.
-/
theorem capDeg_rank_two_rel : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (y : PicSym B.X), B.capDeg_vp p (GlobalTheory.Vert.Model.toQ (R.div 1).cls - GlobalTheory.Vert.Model.toQ (R'.div 0).cls) ((c1 (R.fl.root 0) (R.fl.isLB_root 0) - c1 (R'.fl.root 0) (R'.fl.isLB_root 0)) * y) + B.capDeg_vp p (GlobalTheory.Vert.Model.toQ (R.div 0).cls - GlobalTheory.Vert.Model.toQ (R'.div 0).cls) ((c1 (R'.fl'.root 1) (R'.fl'.isLB_root 1) - c1 (R.fl'.root 0) (R.fl'.isLB_root 0)) * y) = 0 := by
  intro O _ _ _ p _ _ _ B _ W W' ψ R R' y
  obtain ⟨g, u, hg, hu⟩ := GlobalTheory.ClearDenom.exists_smul_eq_genRes_map O B W' W _ _
    R.fl'.isVB_self R.fl.isVB_self ψ.inv
  have := isIso_genRes_map_smulHom W hg
  have : IsIso (B.genRes.map u) := by rw [hu]; infer_instance
  obtain ⟨P, h₁, h₂, hP⟩ := exists_flagPair_ofHom R hg u hu
  obtain ⟨P', h₁', h₂', hP'⟩ := exists_flagPair_ofHom R' hg u hu
  have h := vDeg_rel_of_hom u P P' y
  rw [hP, hP, hP', add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, h₁, h₂, h₁', h₂'] at h
  rw [← map_sub, ← map_sub, capDeg_vp_toQ, capDeg_vp_toQ, ← add_div, h, zero_div]

end GlobalTheory.FlagRankTwoStar
