import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOneStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HenselianAlgClosedResidueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPointStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtendStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecialStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarizationStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.SymB

/- English proof (translation)
Take `⟨M, hM, rfl⟩` from `cls_surj q`. Conclude with `(cls_eq_zero_iff hM).2 (GlobalTheory.ValGenExtend.triv_of_triv_generic R C X XK f j fK H h₁ h₂ h₃ M hM ((cls_eq_zero_iff (pull_isLB hM j)).1 h))`.
-/
theorem pic_inj {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] [Algebra R C] [IsFractionRing R C] {X XK : Scheme.{0}} {f : X ⟶ Sp R} {j : XK ⟶ X}
    {fK : XK ⟶ Sp C} (H : IsPullback j fK f (spMap (algebraMap R C))) (h₁ : Smooth f) (h₂ : QuasiCompact f)
    (h₃ : GeometricallyIntegral f) (q : Pic X) (h : pull j q = 0) : q = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj q
  exact (cls_eq_zero_iff hM).2 (GlobalTheory.ValGenExtend.triv_of_triv_generic R C X XK f j fK H h₁ h₂ h₃ M hM
    ((cls_eq_zero_iff (pull_isLB hM j)).1 h))

/- English proof (translation)
Establish `h` using `isGrpPullback_pullback A s`. Rewrite using `[sqToBase, pull_lam, lift_fst, lift_snd, lam_pull_of_isGrpPullback h]`. Both sides reduce to the same expression.
-/
theorem pull_sq_lam {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) (p : Pic A.left) :
    pull (sqToBase A s) (lam p (fst A A) (snd A A)) =
      lam (pull (pullback.fst A.hom s) p) (fst _ _) (snd _ _) := by
  have h := isGrpPullback_pullback A s
  rw [sqToBase, pull_lam, lift_fst, lift_snd, lam_pull_of_isGrpPullback h]
  rfl

/- English proof (translation)
The claim follows from `congrArg (fun z ↦ z.left) (lift_fst (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))`.
-/
theorem sq_fst {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : sqToBase A s ≫ (fst A A).left =
    (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z ↦ z.left) (lift_fst (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

/- English proof (translation)
The claim follows from `congrArg (fun z ↦ z.left) (lift_snd (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))`.
-/
theorem sq_snd {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : sqToBase A s ≫ (snd A A).left =
    (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z ↦ z.left) (lift_snd (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

/- English proof (translation)
The claim follows from `have hg := isGrpPullback_pullback A s isPullback_prod hg.1 hg.1 (sq_fst A s) (sq_snd A s)`.
-/
theorem isPullback_sq {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) :
    IsPullback (sqToBase A s) ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).hom (A ⊗ A).hom s :=
  have hg := isGrpPullback_pullback A s
  isPullback_prod hg.1 hg.1 (sq_fst A s) (sq_snd A s)

/- English proof (translation)
Establish `h` using `isGrpPullback_pullback A s`. Establish `e` using `map_inv (pushHom h ((Over.pullback s).obj A)) (𝟙 _)`. Establish `e'` using `congrArg (fun q ↦ q.left) e`. Simplify `e'.symm` using `[pushHom, Hom.inv_def, pushPt]`.
-/
theorem inv_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) :
    pullback.fst A.hom s ≫ (GrpObj.inv : A ⟶ A).left =
      (GrpObj.inv : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A).left ≫ pullback.fst A.hom s := by
  have h := isGrpPullback_pullback A s
  have e := map_inv (pushHom h ((Over.pullback s).obj A)) (𝟙 _)
  have e' := congrArg (fun q ↦ q.left) e
  simpa [pushHom, Hom.inv_def, pushPt] using e'.symm

abbrev jj {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : ((Over.pullback s).obj A).left ⟶ A.left := pullback.fst A.hom s

/- English proof (translation)
Establish `hg` using `isGrpPullback_pullback A s`. Set `B` to `(Over.pullback s).obj A`. Set `j : B.left ⟶ A.left` to `pullback.fst A.hom s`. Establish `sq : (s ≫ d.left) ≫ A.hom = 𝟙 S' ≫ s`. Use `Over.w d` as an intermediate fact.

Simplify using `only [Category.assoc, Category.id_comp]`. Rewrite using `[show d.left ≫ A.hom = (𝟙_ (Over S)).hom from this]`. Conclude with `Category.comp_id s`. Set `u : S' ⟶ B.left` to `hg.1.lift (s ≫ d.left) (𝟙 S') sq`. Establish `hu₂ : u ≫ B.hom = 𝟙 S'` using `hg.1.lift_snd _ _ sq`.

Set `t : B ⟶ B` to `Over.homMk (B.hom ≫ u) (by rw [Category.assoc, hu₂, Category.comp_id])`. Establish `ht : t.left ≫ j = j ≫ (toUnit A ≫ d).left`. Establish `e : (toUnit A ≫ d).left = A.hom ≫ d.left` using `rfl`. Establish `e₀ : t.left = B.hom ≫ u` using `rfl`. Establish `e₁ : u ≫ j = s ≫ d.left` using `hg.1.lift_fst _ _ sq`.

Rewrite using `[e, e₀, Category.assoc, e₁, ← Category.assoc, ← Category.assoc]`. Conclude with `congrArg (· ≫ d.left) (hg.1.w).symm`. Set `x₀ : Over.mk (B.hom ≫ s) ⟶ A` to `Over.homMk j hg.1.w`. Set `y₀ : Over.mk (B.hom ≫ s) ⟶ A` to `Over.homMk (j ≫ (toUnit A ≫ d).left) (by`. Rewrite using `[Category.assoc, Over.w]`.

Conclude with `hg.1.w)`. Establish `hτ : (𝟙 B * t).left ≫ j = j ≫ (GlobalTheory.PolTranslate.transl d).left`. Establish `e` using `hg.2 B (𝟙 B) t x₀ y₀ (by simp [x₀, j]) (by simp only [y₀, Over.homMk_left]; exact ht.symm)`. Rewrite using `[← e]`. Establish `: x₀ * y₀ = x₀ ≫ GlobalTheory.PolTranslate.transl d`.

Rewrite using `[GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id]`. Use `congr 1`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `⟨(𝟙 B * t).left, hτ, ?_⟩` and prove the remaining obligations.

Establish `hlift : (lift (𝟙 B) t).left ≫ sqToBase A s = j ≫ (lift (𝟙 A) (toUnit A ≫ d)).left`. Establish `a₁ : (lift (𝟙 B) t).left ≫ (fst B B).left = 𝟙 _` using `congrArg (fun q ↦ q.left) (lift_fst (𝟙 B) t)`. Establish `a₂ : (lift (𝟙 B) t).left ≫ (snd B B).left = t.left` using `congrArg (fun q ↦ q.left) (lift_snd (𝟙 B) t)`. Establish `b₁ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (fst A A).left = 𝟙 _` using `congrArg (fun q ↦ q.left) (lift_fst (𝟙 A) (toUnit A ≫ d))`. Establish `b₂ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (snd A A).left = (toUnit A ≫ d).left` using `congrArg (fun q ↦ q.left) (lift_snd (𝟙 A) (toUnit A ≫ d))`.

Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ (fst A A).left = _ ≫ (fst A A).left`. Rewrite using `[Category.assoc, Category.assoc, b₁, sq_fst, ← Category.assoc, a₁]`. Simplify using `[j]`. Express the relevant statement in the definitionally equal form `_ ≫ (snd A A).left = _ ≫ (snd A A).left`.

Rewrite using `[Category.assoc, Category.assoc, b₂, sq_snd, ← Category.assoc, a₂]`. Conclude with `ht`. Establish `h₀ : ∀ u : S' ⟶ B.left, pull (B.hom ≫ u) l = 0` using `fun u ↦ by`. Rewrite using `[pull_comp, hS (pull u l), map_zero]`. Establish `e₁ : pull t.left l = 0` using `h₀ u`.

Establish `e₂ : pull (1 : B ⟶ B).left l = 0`. Establish `: (1 : B ⟶ B).left = B.hom ≫ (η[B]).left` using `by rw [Hom.one_def]; rfl`. Rewrite using `[this]`. Conclude with `h₀ _`. Establish `e₃ : pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) = lam l (𝟙 B) t`.

Rewrite using `[← pull_comp]`. Establish `: jj A s ≫ (lift (𝟙 A) (toUnit A ≫ d)).left = (lift (𝟙 B) t).left ≫ sqToBase A s` using `hlift.symm`. Rewrite using `[this, pull_comp, h, pull_lam, lift_fst, lift_snd]`. Rewrite using `[e₃, lam, e₁, e₂, Over.id_left, pull_id]`. Normalize the expressions using the abelian group laws.
-/
theorem transl_id {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) (hS : ∀ c : Pic S', c = 0)
    (c : Pic (A ⊗ A).left) (l : Pic ((Over.pullback s).obj A).left)
    (h : pull (sqToBase A s) c = lam l (fst _ _) (snd _ _)) (d : 𝟙_ (Over S) ⟶ A) :
    ∃ τ : ((Over.pullback s).obj A).left ⟶ ((Over.pullback s).obj A).left,
      τ ≫ jj A s = jj A s ≫ (GlobalTheory.PolTranslate.transl d).left ∧
      l = pull τ l - pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) := by
  have hg := isGrpPullback_pullback A s
  let B := (Over.pullback s).obj A
  let j : B.left ⟶ A.left := pullback.fst A.hom s
  have sq : (s ≫ d.left) ≫ A.hom = 𝟙 S' ≫ s := by
    have := Over.w d
    simp only [Category.assoc, Category.id_comp]
    rw [show d.left ≫ A.hom = (𝟙_ (Over S)).hom from this]
    exact Category.comp_id s
  let u : S' ⟶ B.left := hg.1.lift (s ≫ d.left) (𝟙 S') sq
  have hu₂ : u ≫ B.hom = 𝟙 S' := hg.1.lift_snd _ _ sq
  let t : B ⟶ B := Over.homMk (B.hom ≫ u) (by rw [Category.assoc, hu₂, Category.comp_id])
  have ht : t.left ≫ j = j ≫ (toUnit A ≫ d).left := by
    have e : (toUnit A ≫ d).left = A.hom ≫ d.left := rfl
    have e₀ : t.left = B.hom ≫ u := rfl
    have e₁ : u ≫ j = s ≫ d.left := hg.1.lift_fst _ _ sq
    rw [e, e₀, Category.assoc, e₁, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ d.left) (hg.1.w).symm
  let x₀ : Over.mk (B.hom ≫ s) ⟶ A := Over.homMk j hg.1.w
  let y₀ : Over.mk (B.hom ≫ s) ⟶ A := Over.homMk (j ≫ (toUnit A ≫ d).left) (by
    rw [Category.assoc, Over.w]; exact hg.1.w)
  have hτ : (𝟙 B * t).left ≫ j = j ≫ (GlobalTheory.PolTranslate.transl d).left := by
    have e := hg.2 B (𝟙 B) t x₀ y₀ (by simp [x₀, j]) (by simp only [y₀, Over.homMk_left]; exact ht.symm)
    rw [← e]
    have : x₀ * y₀ = x₀ ≫ GlobalTheory.PolTranslate.transl d := by
      rw [GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id]
      congr 1
    rw [this]
    rfl
  refine ⟨(𝟙 B * t).left, hτ, ?_⟩
  have hlift : (lift (𝟙 B) t).left ≫ sqToBase A s = j ≫ (lift (𝟙 A) (toUnit A ≫ d)).left := by
    have a₁ : (lift (𝟙 B) t).left ≫ (fst B B).left = 𝟙 _ := congrArg (fun q ↦ q.left) (lift_fst (𝟙 B) t)
    have a₂ : (lift (𝟙 B) t).left ≫ (snd B B).left = t.left := congrArg (fun q ↦ q.left) (lift_snd (𝟙 B) t)
    have b₁ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun q ↦ q.left) (lift_fst (𝟙 A) (toUnit A ≫ d))
    have b₂ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (snd A A).left = (toUnit A ≫ d).left :=
      congrArg (fun q ↦ q.left) (lift_snd (𝟙 A) (toUnit A ≫ d))
    refine pullback.hom_ext ?_ ?_
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, Category.assoc, b₁, sq_fst, ← Category.assoc, a₁]
      simp [j]
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, Category.assoc, b₂, sq_snd, ← Category.assoc, a₂]
      exact ht
  have h₀ : ∀ u : S' ⟶ B.left, pull (B.hom ≫ u) l = 0 := fun u ↦ by
    rw [pull_comp, hS (pull u l), map_zero]
  have e₁ : pull t.left l = 0 := h₀ u
  have e₂ : pull (1 : B ⟶ B).left l = 0 := by
    have : (1 : B ⟶ B).left = B.hom ≫ (η[B]).left := by rw [Hom.one_def]; rfl
    rw [this]; exact h₀ _
  have e₃ : pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) = lam l (𝟙 B) t := by
    rw [← pull_comp]
    have : jj A s ≫ (lift (𝟙 A) (toUnit A ≫ d)).left = (lift (𝟙 B) t).left ≫ sqToBase A s := hlift.symm
    rw [this, pull_comp, h, pull_lam, lift_fst, lift_snd]
  rw [e₃, lam, e₁, e₂, Over.id_left, pull_id]
  abel

/- English proof (translation)
Introduce `C _ _ R _ _ _ _ _ _ A _ hA c l h y hy hyc`. Take `⟨hH, hk⟩` from `GlobalTheory.T.henselian_alg_closed_residue C R`. Use `haveI := hA.comm`. Establish `hs₀` using `hA.smooth`. Take `⟨V₀, hV₀, e₀⟩` from `GlobalTheory.T.picard_generic_trivial_near_special C R A hA l`.

Take `⟨b₀, hb₀⟩` from `(GlobalTheory.T.section_through_closed_point R A hs₀).2 V₀ hV₀`. Take `⟨b, hb⟩` from `(GlobalTheory.T.section_through_closed_point R A hs₀).1 y hy hyc`. Set `d : 𝟙_ (Over (Sp R)) ⟶ A` to `b⁻¹ * b₀`. Take `⟨τ, hτ, hl⟩` from `transl_id A (spMap (algebraMap R C)) (fun c ↦ GlobalTheory.ThetaExtend.pic_local c) c l h d`. Establish `hbd : b ≫ GlobalTheory.PolTranslate.transl d = b₀`.

Rewrite using `[GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (b ≫ toUnit A) (𝟙 _), Category.id_comp, mul_inv_cancel_left]`. Take `⟨V₂, hy₂, e₂⟩` from `exists_pull_eq_zero (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) y`. Use `⟨(GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂, ⟨?_, hy₂⟩, ?_⟩` and prove the remaining obligations. Use `show (GlobalTheory.PolTranslate.transl d).left y ∈ V₀`. Establish `e : (GlobalTheory.PolTranslate.transl d).left (b.left (IsLocalRing.closedPoint R)) = (b ≫ GlobalTheory.PolTranslate.transl d).left (IsLocalRing.closedPoint R)`.

Rewrite using `[Over.comp_left]`. Both sides reduce to the same expression. Rewrite using `[← hb, e, hbd]`. Conclude with `hb₀`. Use `set W := jj A (spMap (algebraMap R C)) ⁻¹ᵁ ((GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂) with hW`.

Establish `t₁ : pull W.ι (pull τ l) = 0`. Rewrite using `[← pull_comp]`. Use `pull_eq_zero_of_mem (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V₀) (W.ι ≫ τ) (fun z ↦ ?_) e₀` and prove the remaining obligations. Use `show jj A (spMap (algebraMap R C)) ((W.ι ≫ τ) z) ∈ V₀`. Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, hτ, ← Category.assoc, Scheme.Hom.comp_apply]`.

Conclude with `(show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).1`. Establish `t₂ : pull W.ι (pull (jj A (spMap (algebraMap R C))) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) = 0`. Rewrite using `[← pull_comp]`. Conclude with `pull_eq_zero_of_mem V₂ (W.ι ≫ jj A (spMap (algebraMap R C))) (fun z ↦ (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).2) e₂`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem near : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic (A ⊗ A).left)
    (l : Pic ((Over.pullback (spMap (algebraMap R C))).obj A).left),
    pull (sqToBase A (spMap (algebraMap R C))) c = lam l (fst _ _) (snd _ _) →
    ∀ y : A.left, IsClosed {y} → A.hom y = IsLocalRing.closedPoint R →
      ∃ V : A.left.Opens, y ∈ V ∧ pull (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA c l h y hy hyc
  obtain ⟨hH, hk⟩ := GlobalTheory.T.henselian_alg_closed_residue C R
  haveI := hA.comm
  have hs₀ := hA.smooth
  obtain ⟨V₀, hV₀, e₀⟩ := GlobalTheory.T.picard_generic_trivial_near_special C R A hA l
  obtain ⟨b₀, hb₀⟩ := (GlobalTheory.T.section_through_closed_point R A hs₀).2 V₀ hV₀
  obtain ⟨b, hb⟩ := (GlobalTheory.T.section_through_closed_point R A hs₀).1 y hy hyc
  let d : 𝟙_ (Over (Sp R)) ⟶ A := b⁻¹ * b₀
  obtain ⟨τ, hτ, hl⟩ := transl_id A (spMap (algebraMap R C)) (fun c ↦ GlobalTheory.ThetaExtend.pic_local c) c l h d
  have hbd : b ≫ GlobalTheory.PolTranslate.transl d = b₀ := by
    rw [GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      toUnit_unique (b ≫ toUnit A) (𝟙 _), Category.id_comp, mul_inv_cancel_left]
  obtain ⟨V₂, hy₂, e₂⟩ := exists_pull_eq_zero (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) y
  refine ⟨(GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂, ⟨?_, hy₂⟩, ?_⟩
  · show (GlobalTheory.PolTranslate.transl d).left y ∈ V₀
    have e : (GlobalTheory.PolTranslate.transl d).left (b.left (IsLocalRing.closedPoint R)) =
        (b ≫ GlobalTheory.PolTranslate.transl d).left (IsLocalRing.closedPoint R) := by
      rw [Over.comp_left]; rfl
    rw [← hb, e, hbd]
    exact hb₀
  · set W := jj A (spMap (algebraMap R C)) ⁻¹ᵁ ((GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂) with hW
    have t₁ : pull W.ι (pull τ l) = 0 := by
      rw [← pull_comp]
      refine pull_eq_zero_of_mem (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V₀) (W.ι ≫ τ) (fun z ↦ ?_) e₀
      show jj A (spMap (algebraMap R C)) ((W.ι ≫ τ) z) ∈ V₀
      rw [← Scheme.Hom.comp_apply, Category.assoc, hτ, ← Category.assoc, Scheme.Hom.comp_apply]
      exact (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).1
    have t₂ : pull W.ι (pull (jj A (spMap (algebraMap R C))) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) = 0 := by
      rw [← pull_comp]
      exact pull_eq_zero_of_mem V₂ (W.ι ≫ jj A (spMap (algebraMap R C)))
        (fun z ↦ (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).2) e₂
    calc pull W.ι l = pull W.ι (pull τ l - pull (jj A (spMap (algebraMap R C)))
          (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) := congrArg _ hl
      _ = 0 := by rw [map_sub, t₁, t₂, sub_zero]

/- English proof (translation)
Introduce `C _ _ R _ _ _ _ _ _ A _ hA l hn`. Establish `hp₀` using `hA.proper`. Establish `hio` using `GlobalTheory.T.generic_point_open_immersion C R`. Set `j` to `jj A (spMap (algebraMap R C))`. Establish `hjo : IsOpenImmersion j` using `by show IsOpenImmersion (pullback.fst A.hom (spMap (algebraMap R C))) infer_instance`.

Set `U₀ : A.left.Opens` to `j.opensRange`. Set `Q : A.left.Opens → Prop` to `fun W ↦ IsCompact (W : Set A.left) ∧ ∃ (r : ((Over.pullback (spMap (algebraMap R C))).obj A).left ⟶ W.toScheme) (p : Pic W.toScheme), r ≫ W.ι = j ∧ pull r p = l`. Establish `hcA : CompactSpace A.left`. Conclude with `QuasiCompact.compactSpace_of_compactSpace A.hom`. Establish `hcK : CompactSpace ((Over.pullback (spMap (algebraMap R C))).obj A).left` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd A.hom (spMap (algebraMap R C)))`.

Establish `hqs : QuasiSeparatedSpace A.left` using `quasiSeparatedSpace_of_quasiSeparated A.hom`. Establish `base : Q U₀`. Use `⟨?_, j.isoOpensRange.hom, pull j.isoOpensRange.inv l, by simp [U₀], ?_⟩` and prove the remaining obligations. Establish `: (U₀ : Set A.left) = Set.range j` using `Scheme.Hom.coe_opensRange j`. Rewrite using `[this]`.

Conclude with `isCompact_range j.continuous`. Rewrite using `[← pull_comp, Iso.hom_inv_id, pull_id]`. Establish `step : ∀ (W V : A.left.Opens), Q W → IsCompact (V : Set A.left) → pull (j ⁻¹ᵁ V).ι l = 0 → Q (W ⊔ V)`. Introduce and unpack `W V ⟨hW, r, p, hr, hp⟩ hV hl`. Establish `hz : pull (A.left.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0`.

Use `GlobalTheory.T.picard_generic_fibre_injective C R A hA (W ⊓ V) ?_ _ ?_` and prove the remaining obligations. Conclude with `QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW V.isOpen hV`. Establish `e : (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ (W ⊓ V)) ≫ A.left.homOfLE (inf_le_left : W ⊓ V ≤ W) = (j ⁻¹ᵁ (W ⊓ V)).ι ≫ r`. Rewrite using `[← cancel_mono W.ι, Category.assoc, Category.assoc, hr, Scheme.homOfLE_ι]`. Conclude with `morphismRestrict_ι _ _`.

Rewrite using `[← pull_comp, e, pull_comp, hp]`. Conclude with `pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ (W ⊓ V)).ι (fun z ↦ (show _ ∈ W ⊓ V from z.2).2) hl`. Take `⟨q, hq⟩` from `GlobalTheory.T.picard_mayer_vietoris_extend A.left W V p hz`. Use `⟨hW.union hV, r ≫ A.left.homOfLE le_sup_left, q, by simp [hr], ?_⟩` and prove the remaining obligations. Rewrite using `[pull_comp, hq, hp]`.

Establish `hN : ∀ z : A.left, ∃ N : A.left.Opens, z ∈ N ∧ ∀ W, Q W → Q (W ⊔ N)` using `fun z ↦ by`. Take `⟨y, hyz, hy⟩` from `(isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩`. Establish `hyc : A.hom y = IsLocalRing.closedPoint R`. Establish `h₁` using `A.hom.isClosedMap _ hy`. Rewrite `h₁` using `[Set.image_singleton]`.

Establish `h₂` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 h₁`. Conclude with `PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal h₂)`. Take `⟨V, hyV, hV⟩` from `hn y hy hyc`. Take `⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩` from `A.left.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen`. Use `replace hU : IsAffineOpen U := hU`.

Use `⟨U, (specializes_iff_mem_closure.2 hyz).mem_open U.isOpen hyU, fun W hW ↦ step W U hW hU.isCompact ?_⟩` and prove the remaining obligations. Conclude with `pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ U).ι (fun z ↦ hUV z.2) hV`. Use `choose N hz hN using hN`. Take `⟨t, ht⟩` from `CompactSpace.elim_nhds_subcover (fun z ↦ (N z : Set A.left)) (fun z ↦ (N z).isOpen.mem_nhds (hz z))`. Establish `key : ∀ t : Finset A.left, Q (U₀ ⊔ t.sup N)` using `fun t ↦ by classical`.

Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using base`. Consider the case `insert a s _ ih`. Use `hN a _ ih` as an intermediate fact. Rewrite using `[Finset.sup_insert, sup_comm (N a), ← sup_assoc]` and apply the resulting hypothesis.

Establish `htop : U₀ ⊔ t.sup N = ⊤`. Use `top_le_iff.1 fun z _ ↦ ?_` and prove the remaining obligations. Establish `hz' : z ∈ ⋃ x ∈ t, (N x : Set A.left)` using `by rw [ht]; trivial`. Take `⟨x, hx, hzx⟩` from `Set.mem_iUnion₂.1 hz'`. Conclude with `Or.inr (Finset.le_sup (f := N) hx hzx)`.

Establish `hQ` using `key t`. Rewrite `hQ` using `[htop]`. Take `⟨-, r, p, hr, hp⟩` from `hQ`. Use `⟨pull A.left.topIso.inv p, ?_⟩` and prove the remaining obligations. Establish `e : j ≫ A.left.topIso.inv = r`.

Rewrite using `[← hr, Category.assoc]`. Establish `: (⊤ : A.left.Opens).ι = A.left.topIso.hom` using `rfl`. Rewrite using `[this, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[← pull_comp]`. Conclude with `(congrArg (fun q ↦ pull q p) e).trans hp`.
-/
theorem extend : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic ((Over.pullback (spMap (algebraMap R C))).obj A).left,
    (∀ y : A.left, IsClosed {y} → A.hom y = IsLocalRing.closedPoint R →
      ∃ V : A.left.Opens, y ∈ V ∧ pull (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0) →
    ∃ p : Pic A.left, pull (jj A (spMap (algebraMap R C))) p = l := by
  intro C _ _ R _ _ _ _ _ _ A _ hA l hn
  have hp₀ := hA.proper
  have hio := GlobalTheory.T.generic_point_open_immersion C R
  let j := jj A (spMap (algebraMap R C))
  have hjo : IsOpenImmersion j := by
    show IsOpenImmersion (pullback.fst A.hom (spMap (algebraMap R C)))
    infer_instance
  let U₀ : A.left.Opens := j.opensRange
  let Q : A.left.Opens → Prop := fun W ↦ IsCompact (W : Set A.left) ∧
    ∃ (r : ((Over.pullback (spMap (algebraMap R C))).obj A).left ⟶ W.toScheme) (p : Pic W.toScheme), r ≫ W.ι = j ∧ pull r p = l
  have hcA : CompactSpace A.left := by
    exact QuasiCompact.compactSpace_of_compactSpace A.hom
  have hcK : CompactSpace ((Over.pullback (spMap (algebraMap R C))).obj A).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd A.hom (spMap (algebraMap R C)))
  have hqs : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have base : Q U₀ := by
    refine ⟨?_, j.isoOpensRange.hom, pull j.isoOpensRange.inv l, by simp [U₀], ?_⟩
    · have : (U₀ : Set A.left) = Set.range j := Scheme.Hom.coe_opensRange j
      rw [this]
      exact isCompact_range j.continuous
    · rw [← pull_comp, Iso.hom_inv_id, pull_id]
  have step : ∀ (W V : A.left.Opens), Q W → IsCompact (V : Set A.left) → pull (j ⁻¹ᵁ V).ι l = 0 → Q (W ⊔ V) := by
    rintro W V ⟨hW, r, p, hr, hp⟩ hV hl
    have hz : pull (A.left.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0 := by
      refine GlobalTheory.T.picard_generic_fibre_injective C R A hA (W ⊓ V) ?_ _ ?_
      · exact QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW V.isOpen hV
      · have e : (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ (W ⊓ V)) ≫ A.left.homOfLE (inf_le_left : W ⊓ V ≤ W) =
            (j ⁻¹ᵁ (W ⊓ V)).ι ≫ r := by
          rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hr, Scheme.homOfLE_ι]
          exact morphismRestrict_ι _ _
        rw [← pull_comp, e, pull_comp, hp]
        exact pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ (W ⊓ V)).ι (fun z ↦ (show _ ∈ W ⊓ V from z.2).2) hl
    obtain ⟨q, hq⟩ := GlobalTheory.T.picard_mayer_vietoris_extend A.left W V p hz
    refine ⟨hW.union hV, r ≫ A.left.homOfLE le_sup_left, q, by simp [hr], ?_⟩
    rw [pull_comp, hq, hp]
  have hN : ∀ z : A.left, ∃ N : A.left.Opens, z ∈ N ∧ ∀ W, Q W → Q (W ⊔ N) := fun z ↦ by
    obtain ⟨y, hyz, hy⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
    have hyc : A.hom y = IsLocalRing.closedPoint R := by
      have h₁ := A.hom.isClosedMap _ hy
      rw [Set.image_singleton] at h₁
      have h₂ := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 h₁
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal h₂)
    obtain ⟨V, hyV, hV⟩ := hn y hy hyc
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
    replace hU : IsAffineOpen U := hU
    refine ⟨U, (specializes_iff_mem_closure.2 hyz).mem_open U.isOpen hyU, fun W hW ↦ step W U hW hU.isCompact ?_⟩
    exact pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ U).ι (fun z ↦ hUV z.2) hV
  choose N hz hN using hN
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun z ↦ (N z : Set A.left)) (fun z ↦ (N z).isOpen.mem_nhds (hz z))
  have key : ∀ t : Finset A.left, Q (U₀ ⊔ t.sup N) := fun t ↦ by
    classical
    induction t using Finset.induction_on with
    | empty => simpa using base
    | insert a s _ ih =>
      have := hN a _ ih
      rwa [Finset.sup_insert, sup_comm (N a), ← sup_assoc]
  have htop : U₀ ⊔ t.sup N = ⊤ := by
    refine top_le_iff.1 fun z _ ↦ ?_
    have hz' : z ∈ ⋃ x ∈ t, (N x : Set A.left) := by rw [ht]; trivial
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 hz'
    exact Or.inr (Finset.le_sup (f := N) hx hzx)
  have hQ := key t
  rw [htop] at hQ
  obtain ⟨-, r, p, hr, hp⟩ := hQ
  refine ⟨pull A.left.topIso.inv p, ?_⟩
  have e : j ≫ A.left.topIso.inv = r := by
    rw [← hr, Category.assoc]
    have : (⊤ : A.left.Opens).ι = A.left.topIso.hom := rfl
    rw [this, Iso.hom_inv_id, Category.comp_id]
  rw [← pull_comp]
  exact (congrArg (fun q ↦ pull q p) e).trans hp

/- English proof (translation)
Take `⟨w, hw⟩` from `(cls_eq_iff hM (pull_isLB hN (𝟙 _))).1 (e.trans (by rw [cls_pull hN, pull_id]))`. Conclude with `relAmple_pull (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ ↦ trivial) h`.
-/
theorem relAmple_of_cls {K : Type} [CommRing K] (B : Over (Sp K)) {M N : LB B.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : cls M hM = cls N hN) (h : Out.RelAmple B N) : Out.RelAmple B M := by
  obtain ⟨w, hw⟩ := (cls_eq_iff hM (pull_isLB hN (𝟙 _))).1 (e.trans (by rw [cls_pull hN, pull_id]))
  exact relAmple_pull (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ ↦ trivial) h

/- English proof (translation)
Introduce `C _ _ v R _ _ hv A _ hA c hc`. Take `⟨_, _, _, _⟩` from `GlobalTheory.T.valuation_integers_rank_one C v R hv`. Take `⟨hH, hk⟩` from `GlobalTheory.T.henselian_alg_closed_residue C R`. Use `haveI := hA.comm`. Establish `hs₀` using `hA.smooth`.

Establish `hp₀` using `hA.proper`. Establish `hc₀` using `hA.geomConnected`. Establish `hg` using `isGrpPullback_pullback A (spMap (algebraMap R C))`. Establish `hB` using `PolPull.isAbelianScheme_of_isGrpPullback hA hg`. Take `⟨L₀, hL₀, ha₀, hk₀, e₀⟩` from `hc.2.2 C (spMap (algebraMap R C))`.

Take `⟨L', hL', -, hs', ha', -, hl'⟩` from `RiemannExists.exists_sym_translate C _ hB L₀ hL₀ ha₀ hk₀`. Establish `eK : pull (sqToBase A (spMap (algebraMap R C))) c = lam (cls L' hL') (fst _ _) (snd _ _)` using `e₀.trans hl'.symm`. Take `⟨p, hp⟩` from `extend C R A hA (cls L' hL') (near C R A hA c (cls L' hL') eK)`. Take `⟨L, hL, rfl⟩` from `cls_surj p`. Establish `s₂ : Smooth (A ⊗ A).hom`.

Express the relevant statement in the definitionally equal form `Smooth (pullback.fst A.hom A.hom ≫ A.hom)`. Use `infer_instance`. Establish `p₂ : IsProper (A ⊗ A).hom`. Express the relevant statement in the definitionally equal form `IsProper (pullback.fst A.hom A.hom ≫ A.hom)`. Use `infer_instance`.

Establish `c₂ : GeometricallyConnected (A ⊗ A).hom`. Express the relevant statement in the definitionally equal form `GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)`. Conclude with `GeometricallyConnected.comp _ _`. Establish `gi` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected`. Establish `hsq` using `isPullback_sq A (spMap (algebraMap R C))`.

Establish `hlam : lam (cls L hL) (fst A A) (snd A A) = c`. Rewrite using `[← sub_eq_zero]`. Use `pic_inj hsq s₂ inferInstance (gi _ _ _ s₂ c₂) _ ?_` and prove the remaining obligations. Rewrite using `[map_sub, pull_sq_lam, hp, eK, sub_self]`. Establish `hsym : Out.Sym A L`.

Use `GlobalTheory.RigSymSubring.sym_of_cls hL ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `pic_inj hg.1 hs₀ inferInstance (gi _ _ _ hs₀ hc₀) _ ?_` and prove the remaining obligations. Establish `e` using `inv_pull A (spMap (algebraMap R C))`. Rewrite using `[map_sub, ← pull_comp, e, pull_comp, hp, GlobalTheory.RigSymSubring.cls_of_sym hL' hs', sub_self]`.

Take `⟨P, hP, ePc, hPd⟩` from `GlobalTheory.AbDual.principalPol_selfDual hD hC _ A hA c hc`. Establish `hkt : Out.KTriv A L`. Use `GlobalTheory.ThetaExtend.kTriv_of_lam hL hP (ePc.trans hlam.symm) fun T x hx ↦ ?_` and prove the remaining obligations. Establish `ev : ∀ {Y : Over (Sp R)} (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b` using `fun a b ↦ by`. Rewrite using `[evc, ePc, ← hlam, pull_lam, lift_fst, lift_snd]`.

Use `hPd.eq_one x ((triv_ev_iff hP _ _).2 ?_)` and prove the remaining obligations. Rewrite using `[ev, lam_comm, ← ev]`. Conclude with `(triv_ev_iff hP _ _).1 hx`. Use `⟨L, hL, (GlobalTheory.RigSymSubring.rigidified_iff hL).2 (GlobalTheory.ThetaExtend.pic_local _), hsym, ?_, hkt, hlam.symm⟩` and prove the remaining obligations. Establish `hLaws : Out.Laws` using `GlobalTheory.firstFiveLaws.1`.

Use `GlobalTheory.FibreAmple.relAmple_of_fibres hLaws R C A hA L hL ?_ ?_` and prove the remaining obligations. Conclude with `relAmple_of_cls _ (pull_isLB hL _) hL' ((cls_pull hL _ _).trans hp) ha'`. Take `⟨L₁, hL₁, a₁, k₁, e₁⟩` from `hc.2.2 (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R))`. Establish `hB'` using `PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A (spMap (IsLocalRing.residue R)))`. Use `GlobalTheory.T.rel_ample_of_same_polarization _ _ hB' _ L₁ (pull_isLB hL _) hL₁ a₁ k₁ ?_` and prove the remaining obligations.

Rewrite using `[cls_pull hL, ← pull_sq_lam, hlam, e₁]`.
-/
theorem symmetricBundle (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) : SymmetricBundleSt := by
  intro C _ _ v R _ _ hv A _ hA c hc
  obtain ⟨_, _, _, _⟩ := GlobalTheory.T.valuation_integers_rank_one C v R hv
  obtain ⟨hH, hk⟩ := GlobalTheory.T.henselian_alg_closed_residue C R
  haveI := hA.comm
  have hs₀ := hA.smooth
  have hp₀ := hA.proper
  have hc₀ := hA.geomConnected
  have hg := isGrpPullback_pullback A (spMap (algebraMap R C))
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hA hg
  obtain ⟨L₀, hL₀, ha₀, hk₀, e₀⟩ := hc.2.2 C (spMap (algebraMap R C))
  obtain ⟨L', hL', -, hs', ha', -, hl'⟩ := RiemannExists.exists_sym_translate C _ hB L₀ hL₀ ha₀ hk₀
  have eK : pull (sqToBase A (spMap (algebraMap R C))) c = lam (cls L' hL') (fst _ _) (snd _ _) := e₀.trans hl'.symm
  obtain ⟨p, hp⟩ := extend C R A hA (cls L' hL') (near C R A hA c (cls L' hL') eK)
  obtain ⟨L, hL, rfl⟩ := cls_surj p

  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hsq := isPullback_sq A (spMap (algebraMap R C))
  have hlam : lam (cls L hL) (fst A A) (snd A A) = c := by
    rw [← sub_eq_zero]
    refine pic_inj hsq s₂ inferInstance (gi _ _ _ s₂ c₂) _ ?_
    rw [map_sub, pull_sq_lam, hp, eK, sub_self]
  have hsym : Out.Sym A L := by
    refine GlobalTheory.RigSymSubring.sym_of_cls hL ?_
    rw [← sub_eq_zero]
    refine pic_inj hg.1 hs₀ inferInstance (gi _ _ _ hs₀ hc₀) _ ?_
    have e := inv_pull A (spMap (algebraMap R C))
    rw [map_sub, ← pull_comp, e, pull_comp, hp, GlobalTheory.RigSymSubring.cls_of_sym hL' hs', sub_self]
  obtain ⟨P, hP, ePc, hPd⟩ := GlobalTheory.AbDual.principalPol_selfDual hD hC _ A hA c hc
  have hkt : Out.KTriv A L := by
    refine GlobalTheory.ThetaExtend.kTriv_of_lam hL hP (ePc.trans hlam.symm) fun T x hx ↦ ?_
    have ev : ∀ {Y : Over (Sp R)} (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun a b ↦ by
      rw [evc, ePc, ← hlam, pull_lam, lift_fst, lift_snd]
    refine hPd.eq_one x ((triv_ev_iff hP _ _).2 ?_)
    rw [ev, lam_comm, ← ev]
    exact (triv_ev_iff hP _ _).1 hx
  refine ⟨L, hL, (GlobalTheory.RigSymSubring.rigidified_iff hL).2 (GlobalTheory.ThetaExtend.pic_local _), hsym, ?_, hkt, hlam.symm⟩
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  refine GlobalTheory.FibreAmple.relAmple_of_fibres hLaws R C A hA L hL ?_ ?_
  · exact relAmple_of_cls _ (pull_isLB hL _) hL' ((cls_pull hL _ _).trans hp) ha'
  · obtain ⟨L₁, hL₁, a₁, k₁, e₁⟩ := hc.2.2 (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R))
    have hB' := PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A (spMap (IsLocalRing.residue R)))
    refine GlobalTheory.T.rel_ample_of_same_polarization _ _ hB' _ L₁ (pull_isLB hL _) hL₁ a₁ k₁ ?_
    rw [cls_pull hL, ← pull_sq_lam, hlam, e₁]

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.SymB
