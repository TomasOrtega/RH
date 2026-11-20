import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleGenericFibreSpreadsOutStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolSpread

set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K]

def Spreads (R : Type) [CommRing R] [Algebra R K] (T : ∀ (R' : Type) [CommRing R'], (R' →+* K) → Prop) : Prop :=
  ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (ψ : R' →+* K), IsUnit (g f) →
    ψ.comp g = algebraMap R K → T R' ψ

section Shrink

variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/- English proof (translation)
The claim follows from `(IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hf))`.
-/
theorem isUnit_algebraMap {f : R} (hf : f ≠ 0) : IsUnit (algebraMap R K f) :=
  (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hf))

omit [IsDomain R] [IsFractionRing R K] in

/- English proof (translation)
Use `⟨IsLocalization.Away.lift f hg, IsLocalization.Away.lift_comp f hg, ?_⟩` and prove the remaining obligations. Use `IsLocalization.ringHom_ext (Submonoid.powers f) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, IsLocalization.Away.lift_comp, h, h₀]`.
-/
theorem exists_factor {f : R} {ψ₀ : Localization.Away f →+* K} (h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K)
    {R' : Type} [CommRing R'] {g : R →+* R'} {ψ : R' →+* K} (hg : IsUnit (g f)) (h : ψ.comp g = algebraMap R K) :
    ∃ g₁ : Localization.Away f →+* R', g₁.comp (algebraMap R _) = g ∧ ψ.comp g₁ = ψ₀ := by
  refine ⟨IsLocalization.Away.lift f hg, IsLocalization.Away.lift_comp f hg, ?_⟩
  refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, h, h₀]

/- English proof (translation)
Take `⟨f, hf, h⟩` from `h`. Establish `hp : Submonoid.powers f ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hf`. Set `ψ₀ : Localization.Away f →+* K` to `IsLocalization.Away.lift f (isUnit_algebraMap hf)`. Establish `h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K` using `IsLocalization.Away.lift_comp f _`. Use `letI : Algebra (Localization.Away f) K := ψ₀.toAlgebra`.

Use `haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' h₀.symm`. Use `haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hp`. Use `haveI : IsFractionRing (Localization.Away f) K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) _ K`. Take `⟨f', hf', h'⟩` from `H (Localization.Away f) (h _ (algebraMap R _) ψ₀ (IsLocalization.Away.algebraMap_isUnit f) h₀)`. Take `⟨⟨a, s⟩, e⟩` from `IsLocalization.surj (Submonoid.powers f) f'`.

Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `e` using `[map_zero]`. Conclude with `hf' ((IsLocalization.map_units (Localization.Away f) s).mul_left_eq_zero.1 e)`. Use `⟨f * a, mul_ne_zero hf ha, fun R' _ g ψ hg hψ => ?_⟩` and prove the remaining obligations.

Rewrite `hg` using `[map_mul]`. Take `⟨g₁, e₁, e₂⟩` from `exists_factor h₀ (isUnit_of_mul_isUnit_left hg) hψ`. Use `h' R' g₁ ψ ?_ e₂` and prove the remaining obligations. Establish `: g₁ f' * g₁ (algebraMap R _ s) = g a`. Rewrite using `[← map_mul, e, ← e₁]`.

Both sides reduce to the same expression. Conclude with `isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hg)`.
-/
theorem Spreads.step [IsNoetherianRing R] {T T' : ∀ (R' : Type) [CommRing R'], (R' →+* K) → Prop}
    (h : Spreads R T)
    (H : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [Algebra R₁ K] [IsFractionRing R₁ K],
      T R₁ (algebraMap R₁ K) → Spreads R₁ T') : Spreads R T' := by
  obtain ⟨f, hf, h⟩ := h
  have hp : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  let ψ₀ : Localization.Away f →+* K := IsLocalization.Away.lift f (isUnit_algebraMap hf)
  have h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _
  letI : Algebra (Localization.Away f) K := ψ₀.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' h₀.symm
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hp
  haveI : IsFractionRing (Localization.Away f) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) _ K
  obtain ⟨f', hf', h'⟩ := H (Localization.Away f)
    (h _ (algebraMap R _) ψ₀ (IsLocalization.Away.algebraMap_isUnit f) h₀)
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) f'
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    exact hf' ((IsLocalization.map_units (Localization.Away f) s).mul_left_eq_zero.1 e)
  refine ⟨f * a, mul_ne_zero hf ha, fun R' _ g ψ hg hψ => ?_⟩
  rw [map_mul] at hg
  obtain ⟨g₁, e₁, e₂⟩ := exists_factor h₀ (isUnit_of_mul_isUnit_left hg) hψ
  refine h' R' g₁ ψ ?_ e₂
  have : g₁ f' * g₁ (algebraMap R _ s) = g a := by
    rw [← map_mul, e, ← e₁]; rfl
  exact isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hg)

end Shrink

variable (P : Out.PolAV (Sp K))

def GrpModel {R : Type} [CommRing R] (ψ : R →+* K) (A : Over (Sp R)) [GrpObj A] (φ : P.A.left ⟶ A.left) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension P.g A.hom ∧ IsGrpPullback P.A A (spMap ψ) φ

variable {P}

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (g : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp g) = spMap ψ ≫ spMap g := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Take `⟨hA, hs, hp⟩` from `h`. Establish `e' : spMap ψ₀ = spMap ψ ≫ spMap g` using `by rw [← e, spMap_comp]`. Establish `w : φ ≫ A.hom = (P.A.hom ≫ spMap ψ) ≫ spMap g` using `by rw [hp.1.w, e', Category.assoc]`. Establish `hb` using `isGrpPullback_pullback A (spMap g)`. Use `⟨pullback.lift φ _ w, pullback.lift_fst _ _ _, PolPull.isAbelianScheme_of_isGrpPullback hA hb, (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hb.1 hs, ?_⟩` and prove the remaining obligations.

Conclude with `hb.cancel (hp.congr e' (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)`.
-/
theorem GrpModel.baseChange {R R' : Type} [CommRing R] [CommRing R'] {ψ₀ : R →+* K} {A : Over (Sp R)} [GrpObj A]
    {φ : P.A.left ⟶ A.left} (h : GrpModel P ψ₀ A φ) {g : R →+* R'} {ψ : R' →+* K} (e : ψ.comp g = ψ₀) :
    ∃ φ' : P.A.left ⟶ ((Over.pullback (spMap g)).obj A).left,
      φ' ≫ pullback.fst A.hom (spMap g) = φ ∧ GrpModel P ψ ((Over.pullback (spMap g)).obj A) φ' := by
  obtain ⟨hA, hs, hp⟩ := h
  have e' : spMap ψ₀ = spMap ψ ≫ spMap g := by rw [← e, spMap_comp]
  have w : φ ≫ A.hom = (P.A.hom ≫ spMap ψ) ≫ spMap g := by rw [hp.1.w, e', Category.assoc]
  have hb := isGrpPullback_pullback A (spMap g)
  refine ⟨pullback.lift φ _ w, pullback.lift_fst _ _ _, PolPull.isAbelianScheme_of_isGrpPullback hA hb,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hb.1 hs, ?_⟩
  exact hb.cancel (hp.congr e' (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

/- English proof (translation)
The claim follows from `LBIso.trans hM (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) h (GenSpread.lbIso_pull_pull hL φ' e.symm)`.
-/
theorem lbIso_baseChange {X Y Z : Scheme.{0}} {M : LB Z} {L : LB X} (hM : M.IsLB) (hL : L.IsLB) {φ : Z ⟶ X}
    {φ' : Z ⟶ Y} {π : Y ⟶ X} (e : φ' ≫ π = φ) (h : LBIso M (L.pull φ)) : LBIso M ((L.pull π).pull φ') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) h (GenSpread.lbIso_pull_pull hL φ' e.symm)

variable (P)

def HasGrp (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : P.A.left ⟶ A.left), GrpModel P ψ A φ

def HasLB (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : P.A.left ⟶ A.left) (L : LB A.left),
    GrpModel P ψ A φ ∧ L.IsLB ∧ LBIso P.L (L.pull φ)

def HasAmple (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : P.A.left ⟶ A.left) (L : LB A.left),
    GrpModel P ψ A φ ∧ L.IsLB ∧ LBIso P.L (L.pull φ) ∧ Out.RelAmple A L

def HasPol (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (P' : Out.PolAV (Sp R)) (φ : P.A.left ⟶ P'.A.left),
    P'.g = P.g ∧ IsGrpPullback P.A P'.A (spMap ψ) φ ∧ LBIso P.L (P'.L.pull φ)

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra R K] [IsFractionRing R K]

/- English proof (translation)
Take `⟨f, hf, ψ₀, A, _, φ, h₀, h⟩` from `GlobalTheory.SpreadAb.exists_abelianScheme_away R K P`. Use `⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩` and prove the remaining obligations. Take `⟨g₁, -, e₂⟩` from `exists_factor h₀ hg hψ`. Take `⟨φ', -, h'⟩` from `GrpModel.baseChange (P := P) h e₂`. Conclude with `⟨_, _, φ', h'⟩`.
-/
theorem spreads_grp : Spreads R (HasGrp P) := by
  obtain ⟨f, hf, ψ₀, A, _, φ, h₀, h⟩ := GlobalTheory.SpreadAb.exists_abelianScheme_away R K P
  refine ⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩
  obtain ⟨g₁, -, e₂⟩ := exists_factor h₀ hg hψ
  obtain ⟨φ', -, h'⟩ := GrpModel.baseChange (P := P) h e₂
  exact ⟨_, _, φ', h'⟩

/- English proof (translation)
Take `⟨A, _, φ, h⟩` from `h`. Use `h.1.proper` as an intermediate fact. Set `i` to `h.2.2.1.isoPullback`. Take `⟨f, hf, M, hM, H⟩` from `GlobalTheory.T.lineBundle_generic_fibre_spreads_out R K A.left A.hom (P.L.pull i.inv) inferInstance inferInstance (pull_isLB P.isLB _)`. Set `ψ₀ : Localization.Away f →+* K` to `IsLocalization.Away.lift f (isUnit_algebraMap hf)`.

Establish `h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K` using `IsLocalization.Away.lift_comp f _`. Take `⟨φ₁, e₁, h₁⟩` from `h.baseChange h₀`. Establish `H₁` using `H (i.inv ≫ φ₁) (by`. Rewrite using `[Category.assoc]`. Conclude with `(congrArg (i.inv ≫ ·) e₁).trans (h.2.2.1.isoPullback_inv_fst))`.

Establish `H₂ : LBIso P.L (M.pull φ₁)`. Establish `a` using `(CechPic.cls_eq_iff (pull_isLB P.isLB _) (pull_isLB hM _)).2 H₁`. Use `(CechPic.cls_eq_iff P.isLB (pull_isLB hM _)).1 ?_` and prove the remaining obligations. Establish `b` using `congrArg (CechPic.pull i.hom) a`. Rewrite `b` using `[CechPic.cls_pull P.isLB, CechPic.cls_pull hM, ← CechPic.pull_comp, ← CechPic.pull_comp, i.hom_inv_id, CechPic.pull_id, i.hom_inv_id_assoc]`.

Conclude with `b`. Use `⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩` and prove the remaining obligations. Take `⟨g₁, -, e₂⟩` from `exists_factor h₀ hg hψ`. Take `⟨φ', e', h'⟩` from `h₁.baseChange e₂`. Conclude with `⟨_, _, φ', M.pull (pullback.fst _ _), h', pull_isLB hM _, lbIso_baseChange P.isLB hM e' H₂⟩`.
-/
theorem spreads_lb (h : HasGrp P R (algebraMap R K)) : Spreads R (HasLB P) := by
  obtain ⟨A, _, φ, h⟩ := h
  have := h.1.proper
  let i := h.2.2.1.isoPullback
  obtain ⟨f, hf, M, hM, H⟩ := GlobalTheory.T.lineBundle_generic_fibre_spreads_out R K A.left A.hom (P.L.pull i.inv) inferInstance inferInstance
    (pull_isLB P.isLB _)
  let ψ₀ : Localization.Away f →+* K := IsLocalization.Away.lift f (isUnit_algebraMap hf)
  have h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _
  obtain ⟨φ₁, e₁, h₁⟩ := h.baseChange h₀
  have H₁ := H (i.inv ≫ φ₁) (by
    rw [Category.assoc]
    exact (congrArg (i.inv ≫ ·) e₁).trans (h.2.2.1.isoPullback_inv_fst))
  have H₂ : LBIso P.L (M.pull φ₁) := by
    have a := (CechPic.cls_eq_iff (pull_isLB P.isLB _) (pull_isLB hM _)).2 H₁
    refine (CechPic.cls_eq_iff P.isLB (pull_isLB hM _)).1 ?_
    have b := congrArg (CechPic.pull i.hom) a
    rw [CechPic.cls_pull P.isLB, CechPic.cls_pull hM, ← CechPic.pull_comp, ← CechPic.pull_comp, i.hom_inv_id,
      CechPic.pull_id, i.hom_inv_id_assoc] at b
    exact b
  refine ⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩
  obtain ⟨g₁, -, e₂⟩ := exists_factor h₀ hg hψ
  obtain ⟨φ', e', h'⟩ := h₁.baseChange e₂
  exact ⟨_, _, φ', M.pull (pullback.fst _ _), h', pull_isLB hM _, lbIso_baseChange P.isLB hM e' H₂⟩

/- English proof (translation)
Take `⟨A, _, φ, L, h, hL, e⟩` from `h`. Use `h.1.proper` as an intermediate fact. Set `i` to `h.2.2.1.isoPullback`. Establish `hi : IsPullback i.inv (pullback.snd A.hom (spMap (algebraMap R K))) P.A.hom (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact h.2.2.1.isoPullback_inv_snd⟩`. Take `⟨w, hw⟩` from `(GenSpread.lbIso_pull_of_lbIso e i.inv h.2.2.1.isoPullback_inv_fst.symm).symm`.

Take `⟨f, hf, H⟩` from `GlobalTheory.AmpleSpread.relAmple_spread R K A L inferInstance hL (relAmple_pull (A' := Over.mk (pullback.snd A.hom (spMap (algebraMap R K)))) hi P.isLB (pull_isLB hL _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample)`. Use `⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩` and prove the remaining obligations. Take `⟨φ', e', h'⟩` from `h.baseChange hψ`. Conclude with `⟨_, _, φ', L.pull (pullback.fst _ _), h', pull_isLB hL _, lbIso_baseChange P.isLB hL e' e, H R' g hg⟩`.
-/
theorem spreads_ample (h : HasLB P R (algebraMap R K)) : Spreads R (HasAmple P) := by
  obtain ⟨A, _, φ, L, h, hL, e⟩ := h
  have := h.1.proper
  let i := h.2.2.1.isoPullback
  have hi : IsPullback i.inv (pullback.snd A.hom (spMap (algebraMap R K))) P.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact h.2.2.1.isoPullback_inv_snd⟩
  obtain ⟨w, hw⟩ := (GenSpread.lbIso_pull_of_lbIso e i.inv h.2.2.1.isoPullback_inv_fst.symm).symm
  obtain ⟨f, hf, H⟩ := GlobalTheory.AmpleSpread.relAmple_spread R K A L inferInstance hL
    (relAmple_pull (A' := Over.mk (pullback.snd A.hom (spMap (algebraMap R K)))) hi P.isLB (pull_isLB hL _)
      ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample)
  refine ⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩
  obtain ⟨φ', e', h'⟩ := h.baseChange hψ
  exact ⟨_, _, φ', L.pull (pullback.fst _ _), h', pull_isLB hL _, lbIso_baseChange P.isLB hL e' e, H R' g hg⟩

omit [IsDomain R] [IsNoetherianRing R] [Algebra R K] [IsFractionRing R K] in

/- English proof (translation)
Take `⟨U, hU, ht⟩` from `P.sym (default : PrimeSpectrum K)`. Establish `: Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Take `rfl : U = ⊤` from `top_le_iff.1 fun y _ => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]`. Establish `a` using `(CechPic.cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ht`. Rewrite `a` using `[CechPic.cls_linComb P.isLB, Fin.sum_univ_two]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, Matrix.cons_val_fin_one] at a`. Establish `hj : ∃ j : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, j ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _` using `⟨P.A.left.topIso.inv, P.A.left.toIso_inv_ι⟩`. Take `⟨j, c⟩` from `hj`. Establish `b` using `congrArg (CechPic.pull j) (add_neg_eq_zero.1 a)`. Rewrite `b` using `[← CechPic.pull_comp, ← CechPic.pull_comp, ← Category.assoc, c, Category.id_comp, CechPic.pull_id]`. Then use the resulting hypothesis.
-/
theorem cls_inv : CechPic.pull (GrpObj.inv : P.A ⟶ P.A).left (CechPic.cls P.L P.isLB) = CechPic.cls P.L P.isLB := by
  obtain ⟨U, hU, ht⟩ := P.sym (default : PrimeSpectrum K)
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]
  have a := (CechPic.cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ht
  rw [CechPic.cls_linComb P.isLB, Fin.sum_univ_two] at a
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, Matrix.cons_val_fin_one] at a
  have hj : ∃ j : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, j ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.toIso_inv_ι⟩
  obtain ⟨j, c⟩ := hj
  have b := congrArg (CechPic.pull j) (add_neg_eq_zero.1 a)
  rwa [← CechPic.pull_comp, ← CechPic.pull_comp, ← Category.assoc, c, Category.id_comp, CechPic.pull_id] at b

/- English proof (translation)
Use `fun s => ⟨⊤, trivial, (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_⟩` and prove the remaining obligations. Rewrite using `[CechPic.cls_linComb hL, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, CechPic.pull_comp, h, Matrix.cons_val_fin_one, add_neg_cancel]`.
-/
theorem sym_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : CechPic.pull (GrpObj.inv : A ⟶ A).left (CechPic.cls L hL) = CechPic.cls L hL) : Out.Sym A L := by
  refine fun s => ⟨⊤, trivial, (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_⟩
  rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, CechPic.pull_comp, h,
    Matrix.cons_val_fin_one, add_neg_cancel]

/- English proof (translation)
Take `⟨A, _, φ, L, h, hL, e, hA⟩` from `h`. Use `h.1.proper` as an intermediate fact. Establish `ec` using `(CechPic.cls_eq_iff P.isLB (pull_isLB hL _)).2 e`. Rewrite `ec` using `[CechPic.cls_pull hL]`. Take `⟨i, hi⟩` from `exists_chart hL (eSec A (genericPoint (Sp R)))`.

Take `⟨f₁, hf₁, H₁⟩` from `GenSpread.exists_forall_mem (R := R) (V := eSec A ⁻¹ᵁ L.U i) hi`. Take `⟨f₂, hf₂, H₂⟩` from `GenSpread.exists_lbIso A.hom h.2.2.1 (pull_isLB hL (GrpObj.inv : A ⟶ A).left) hL (by`. Use `(CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)).1 ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL, ← CechPic.pull_comp, ← PolBaseChange.inv_comm h.2.2, CechPic.pull_comp, ← ec, cls_inv])`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : LBIso (L.pull φ) (P.L.pull (𝟙 _)) := by`.

Use `(CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB P.isLB _)).1 ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull hL, CechPic.cls_pull P.isLB, CechPic.pull_id, ec]`. Take `⟨f₃, hf₃, H₃⟩` from `GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K (algebraMap R K) P.A φ h.1 hL hA h.2.2 (kTriv_pull (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A)))) P.isLB (pull_isLB hL _) ((isGen_iff w).1 hw) P.ktriv)`. Establish `hf₃' : f₃ ≠ 0` using `by rintro rfl; exact hf₃ (map_zero _)`. Use `⟨f₁ * f₂ * f₃, mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃', fun R' _ g ψ hg hψ => ?_⟩` and prove the remaining obligations.

Rewrite `hg` using `[map_mul, map_mul]`. Establish `u₁` using `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hg)`. Establish `u₂` using `isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hg)`. Establish `u₃` using `isUnit_of_mul_isUnit_right hg`. Take `⟨φ', e', h'⟩` from `h.baseChange hψ`.

Establish `hb` using `isGrpPullback_pullback A (spMap g)`. Establish `hL'` using `pull_isLB hL (pullback.fst A.hom (spMap g))`. Take `⟨w', hw'⟩` from `PolBaseChange.lbIso_refl hL'`. Use `⟨{ A := (Over.pullback (spMap g)).obj A isAb := h'.1 g := P.g smoothDim := h'.2.1 L := L.pull (pullback.fst A.hom (spMap g)) isLB := hL' rigid := ?_ sym := ?_ ample := relAmple_pull hb.1 hL hL' ((isGen_iff w').1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) hA ktriv := H₃ R' g _ …` and prove the remaining obligations. Use `IsoExtend.exists_gen_of_chart hL' _ (fun _ => i) fun y => mem_pull.2 ?_` and prove the remaining obligations.

Conclude with `(congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm hb)).mpr (H₁ R' g u₁ y)`. Use `sym_of_cls hL' ?_` and prove the remaining obligations. Establish `a` using `(CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) hL').2 (H₂ R' g u₂ _ _ _ hb.1.w)`. Rewrite `a` using `[CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL, ← CechPic.pull_comp, ← PolBaseChange.inv_comm hb, CechPic.pull_comp]`. Conclude with `a`.
-/
theorem spreads_pol (h : HasAmple P R (algebraMap R K)) : Spreads R (HasPol P) := by
  obtain ⟨A, _, φ, L, h, hL, e, hA⟩ := h
  have := h.1.proper
  have ec := (CechPic.cls_eq_iff P.isLB (pull_isLB hL _)).2 e
  rw [CechPic.cls_pull hL] at ec

  obtain ⟨i, hi⟩ := exists_chart hL (eSec A (genericPoint (Sp R)))
  obtain ⟨f₁, hf₁, H₁⟩ := GenSpread.exists_forall_mem (R := R) (V := eSec A ⁻¹ᵁ L.U i) hi

  obtain ⟨f₂, hf₂, H₂⟩ := GenSpread.exists_lbIso A.hom h.2.2.1 (pull_isLB hL (GrpObj.inv : A ⟶ A).left) hL (by
    refine (CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)).1 ?_
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL, ← CechPic.pull_comp,
      ← PolBaseChange.inv_comm h.2.2, CechPic.pull_comp, ← ec, cls_inv])

  obtain ⟨w, hw⟩ : LBIso (L.pull φ) (P.L.pull (𝟙 _)) := by
    refine (CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB P.isLB _)).1 ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull P.isLB, CechPic.pull_id, ec]
  obtain ⟨f₃, hf₃, H₃⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K (algebraMap R K) P.A φ h.1 hL hA h.2.2
    (kTriv_pull (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A)))) P.isLB (pull_isLB hL _) ((isGen_iff w).1 hw) P.ktriv)
  have hf₃' : f₃ ≠ 0 := by rintro rfl; exact hf₃ (map_zero _)
  refine ⟨f₁ * f₂ * f₃, mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃', fun R' _ g ψ hg hψ => ?_⟩
  rw [map_mul, map_mul] at hg
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hg)
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hg)
  have u₃ := isUnit_of_mul_isUnit_right hg
  obtain ⟨φ', e', h'⟩ := h.baseChange hψ
  have hb := isGrpPullback_pullback A (spMap g)
  have hL' := pull_isLB hL (pullback.fst A.hom (spMap g))
  obtain ⟨w', hw'⟩ := PolBaseChange.lbIso_refl hL'
  refine ⟨{ A := (Over.pullback (spMap g)).obj A
            isAb := h'.1
            g := P.g
            smoothDim := h'.2.1
            L := L.pull (pullback.fst A.hom (spMap g))
            isLB := hL'
            rigid := ?_
            sym := ?_
            ample := relAmple_pull hb.1 hL hL' ((isGen_iff w').1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
            ktriv := H₃ R' g _ _ u₃ hb }, φ', rfl, h'.2.2, lbIso_baseChange P.isLB hL e' e⟩
  · refine IsoExtend.exists_gen_of_chart hL' _ (fun _ => i) fun y => mem_pull.2 ?_
    exact (congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm hb)).mpr (H₁ R' g u₁ y)
  · refine sym_of_cls hL' ?_
    have a := (CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) hL').2 (H₂ R' g u₂ _ _ _ hb.1.w)
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL, ← CechPic.pull_comp,
      ← PolBaseChange.inv_comm hb, CechPic.pull_comp] at a
    exact a

end GlobalTheory.PolSpread

open GlobalTheory.PolSpread in

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ P`. Take `⟨f, hf, H⟩` from `(((spreads_grp P R).step (spreads_lb P)).step (spreads_ample P)).step (spreads_pol P)`. Establish `h₀ : (IsLocalization.Away.lift f (isUnit_algebraMap (K` using `K) hf) : Localization.Away f →+* K).comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _`. Take `⟨P', φ, h⟩` from `H _ _ _ (IsLocalization.Away.algebraMap_isUnit f) h₀`. Conclude with `⟨f, hf, _, P', φ, h₀, h⟩`.
-/
theorem GlobalTheory.polAV_spread : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp K)), ∃ (f : R) (_ : f ≠ 0) (ψ : (Localization.Away f) →+* K) (P' : Out.PolAV (Sp (Localization.Away f))) (φ : P.A.left ⟶ P'.A.left), ψ.comp (algebraMap R _) = algebraMap R K ∧ P'.g = P.g ∧ IsGrpPullback P.A P'.A (spMap ψ) φ ∧ LBIso P.L (P'.L.pull φ) := by
  intro R K _ _ _ _ _ _ P
  obtain ⟨f, hf, H⟩ := (((spreads_grp P R).step (spreads_lb P)).step (spreads_ample P)).step (spreads_pol P)
  have h₀ : (IsLocalization.Away.lift f (isUnit_algebraMap (K := K) hf) : Localization.Away f →+* K).comp
      (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _
  obtain ⟨P', φ, h⟩ := H _ _ _ (IsLocalization.Away.algebraMap_isUnit f) h₀
  exact ⟨f, hf, _, P', φ, h₀, h⟩
