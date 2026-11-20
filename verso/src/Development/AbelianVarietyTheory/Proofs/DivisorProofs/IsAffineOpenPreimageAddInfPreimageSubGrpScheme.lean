import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SumAffine

/- English proof (translation)
Use `⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]`. Simplify using the standard rewrite rules. Use `ext`.

Simplify using `[MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]`. Simplify using the standard rewrite rules.
-/
theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A T : C) [GrpObj A]
    (b : T ⟶ A) : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)) := by
  refine ⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp

/- English proof (translation)
Use `haveI : IsAffine (Sp R) := by unfold Sp; infer_instance`. Use `haveI : IsAffineHom T.hom := inferInstance`. Use `haveI : IsAffineHom (fst A T).left := by`. Express the relevant statement in the definitionally equal form `IsAffineHom (pullback.fst A.hom T.hom)`. Conclude with `isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance`.

Use `haveI := isIso_shear A T b`. Establish `h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T` using `by simp`. Use `haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by`. Rewrite using `[h, Over.comp_left]`. Use `haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left := inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))`.

Use `infer_instance`. Conclude with `hV.preimage _`.
-/
theorem isAffineOpen_preimage_translate (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R)) [IsAffine T.left] (b : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ b)).left ⁻¹ᵁ V) := by
  haveI : IsAffine (Sp R) := by unfold Sp; infer_instance
  haveI : IsAffineHom T.hom := inferInstance
  haveI : IsAffineHom (fst A T).left := by
    change IsAffineHom (pullback.fst A.hom T.hom)
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance
  haveI := isIso_shear A T b
  have h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T := by simp
  haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by
    rw [h, Over.comp_left]
    haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left :=
      inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))
    infer_instance
  exact hV.preimage _

/- English proof (translation)
Establish `h1` using `isAffineOpen_preimage_translate R A V hV T a`. Establish `h2` using `isAffineOpen_preimage_translate R A V hV T a⁻¹`. Rewrite `h2` using `[GrpObj.comp_inv]`. Use `haveI : IsSeparated (snd A T).left := by`. Express the relevant statement in the definitionally equal form `IsSeparated (pullback.snd A.hom T.hom)`.

Use `infer_instance`. Use `haveI : (A ⊗ T).left.IsSeparated := by`. Rewrite using `[Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]`. Use `infer_instance`. Conclude with `h1.inf h2`.
-/
theorem isAffineOpen_preimage_add_inf_preimage_sub (R : Type) [CommRing R] (A : Over (Sp R))
    [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R))
    [IsAffine T.left] (a : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓
      (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  have h1 := isAffineOpen_preimage_translate R A V hV T a
  have h2 := isAffineOpen_preimage_translate R A V hV T a⁻¹
  rw [GrpObj.comp_inv] at h2
  haveI : IsSeparated (snd A T).left := by
    change IsSeparated (pullback.snd A.hom T.hom)
    infer_instance
  haveI : (A ⊗ T).left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]
    infer_instance
  exact h1.inf h2

end GlobalTheory.SumAffine
