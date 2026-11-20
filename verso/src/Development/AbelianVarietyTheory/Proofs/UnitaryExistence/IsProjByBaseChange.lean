import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
namespace GlobalTheory.AbLaw.BaseChange

/- English proof (translation)
Establish `h` using `congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).hom r)`. Simplify using `only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h ⊢`. Rewrite using `[h]`.
-/
theorem cst_comp_specMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f' : X ⟶ Spec (CommRingCat.of R')) (W : X.Opens) (r : R) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) W r = cst f' W (g r) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).hom r)
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  rw [h]

/- English proof (translation)
Take `⟨r, rfl⟩` from `(cst_bijective (𝟙 (Spec (CommRingCat.of R))) (W := ⊤) rfl).2 d`. Conclude with `⟨r, by rw [ap_cst, Category.comp_id]⟩`.
-/
theorem ap_top_eq_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {W : X.Opens} (h : W ≤ f ⁻¹ᵁ ⊤) (d : Γ(Spec (CommRingCat.of R), ⊤)) :
    ∃ r, ap f h d = cst f W r := by
  obtain ⟨r, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of R))) (W := ⊤) rfl).2 d
  exact ⟨r, by rw [ap_cst, Category.comp_id]⟩

end GlobalTheory.AbLaw.BaseChange

open GlobalTheory.AbLaw.BaseChange in

/- English proof (translation)
Introduce `R R' _ _ g X X' f p q sq hf`. Take `⟨H, hH, m, s, hs, hs'⟩` from `hf`. Establish `hloc : ∀ a, nonzeroLocus (boxSec p q (s a) (oneSec _)) = p ⁻¹ᵁ nonzeroLocus (s a) ⊓ q ⁻¹ᵁ ⊤` using `fun a => by`. Rewrite using `[nonzeroLocus_boxSec, nonzeroLocus_oneSec]`. Use `⟨box p q H (Inh.trivLB _), isLB_box p q hH (Inh.trivLB_isLB _), m, fun a => boxSec p q (s a) (oneSec _), ?_, fun a => ?_⟩` and prove the remaining obligations.

Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[hloc]`. Conclude with `⟨hi, trivial⟩`.

Take `⟨aff₁, r₁, hr₁, sj₁⟩` from `hs' a`. Establish `aff₂ : IsAffineOpen (⊤ : (Spec (CommRingCat.of R')).Opens)` using `isAffineOpen_top _`. Establish `loc` using `hloc a`. Establish `l₁` using `loc.le.trans inf_le_left`. Establish `l₂` using `loc.le.trans inf_le_right`.

Use `⟨?_, fun b => ap p l₁ (r₁ b), fun b k => ?_, ?_⟩` and prove the remaining obligations. Establish `: IsAffine _` using `aff₁`. Establish `: IsAffine _` using `aff₂`. Establish `: IsAffine _` using `isAffineOpen_top (Spec (CommRingCat.of R))`. Conclude with `.of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom`.

Use `(rs_mul p q _ _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (rs_ap p _ _ _) (rs_mul p q _ _ _ _ _)).symm)` and prove the remaining obligations. Conclude with `(congrArg (· * _) (ap_ratio p (hr₁ b k.1) _ _)).trans (_root_.mul_assoc _ _ _)`. Establish `po` using `(isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1 (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)`. Rewrite using `[← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]`. Introduce and unpack `_ (⟨d, rfl⟩ | ⟨d, rfl⟩)`.

Take `⟨F, rfl⟩` from `sj₁ d`. Express the relevant statement in the definitionally equal form `ap p l₁ _ ∈ _`. Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨MvPolynomial.C (g c), by`. Rewrite using `[MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w, cst_comp_specMap]⟩`.

Consider the case `add F G hF hG => rw [map_add, map_add]`. Conclude with `Subring.add_mem _ hF hG`. Consider the case `mul_X F i hF`. Rewrite using `[map_mul, map_mul]`. Use `Subring.mul_mem _ hF ⟨MvPolynomial.X i, ?_⟩` and prove the remaining obligations.

Simplify using `only [MvPolynomial.eval₂Hom_X']`. Express the relevant statement in the definitionally equal form `ap q l₂ _ ∈ _`. Take `⟨r, hr⟩` from `ap_top_eq_cst q l₂ d`. Conclude with `⟨MvPolynomial.C r, by rw [MvPolynomial.eval₂Hom_C, hr]⟩`.
-/
theorem GlobalTheory.AbLaw.isProjBy_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsProjBy f → IsProjBy f' := by
  intro R R' _ _ g X X' f p q sq hf
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  have hloc : ∀ a, nonzeroLocus (boxSec p q (s a) (oneSec _)) = p ⁻¹ᵁ nonzeroLocus (s a) ⊓ q ⁻¹ᵁ ⊤ := fun a => by
    rw [nonzeroLocus_boxSec, nonzeroLocus_oneSec]
  refine ⟨box p q H (Inh.trivLB _), isLB_box p q hH (Inh.trivLB_isLB _), m,
    fun a => boxSec p q (s a) (oneSec _), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [hloc]
    exact ⟨hi, trivial⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' a
  have aff₂ : IsAffineOpen (⊤ : (Spec (CommRingCat.of R')).Opens) := isAffineOpen_top _
  have loc := hloc a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => ap p l₁ (r₁ b), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_ap p _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg (· * _) (ap_ratio p (hr₁ b k.1) _ _)).trans (_root_.mul_assoc _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C (g c), by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w, cst_comp_specMap]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X i, ?_⟩
        simp only [MvPolynomial.eval₂Hom_X']
    · change ap q l₂ _ ∈ _
      obtain ⟨r, hr⟩ := ap_top_eq_cst q l₂ d
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.eval₂Hom_C, hr]⟩
