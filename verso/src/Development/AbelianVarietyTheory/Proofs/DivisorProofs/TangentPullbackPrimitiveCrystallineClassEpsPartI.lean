import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEqStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using `[epsHom, DualNumber.lift_apply_apply]`.
-/
theorem snd_epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

/- English proof (translation)
Use extensionality with `r`. Simplify using `[epsHom, DualNumber.lift_apply_apply]`. Simplify using `[AlgHom.comp_apply, snd_epsHom]`.
-/
theorem epsHom_comp_inl {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ := by
  ext r
  · simp [epsHom, DualNumber.lift_apply_apply]
  · simp [AlgHom.comp_apply, snd_epsHom]

/- English proof (translation)
Apply `DualNumber.algHom_ext` to reduce the goal to its premises. Simplify using `[epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply]`.
-/
theorem epsHom_comp_epsMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' := by
  apply DualNumber.algHom_ext
  simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply]

/- English proof (translation)
Apply the tactic sequence `ext1 <;> simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]`.
-/
theorem ptV_eq {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D]
    (x : Pt A D) : ptV v x = (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x) *
      (spOver (EpsWeil.epsMap R D) ≫ CartesianMonoidalCategory.lift 1 v) := by
  ext1 <;> simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]

/- English proof (translation)
Simplify using `[pt0, comp_lift]`.
-/
theorem specOverOfAlgHom_comp_pointWithZeroSecondCoord {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {D D' : Type} [CommRing D] [Algebra R D] [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) : spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x) := by
  simp [pt0, comp_lift]

/- English proof (translation)
Introduce `R _ A B _ _ f hf v`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R (A ⊗ B) f hf`. Establish `hc` using `(GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R (A ⊗ B) f).1`. Set `V1 : Pt (A ⊗ B) (DualNumber R)` to `CartesianMonoidalCategory.lift 1 v`. Use `⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x) (spOver (EpsWeil.epsMap R D) ≫ V1) + fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) + fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩` and prove the remaining obligations.

Introduce `D _ _ D' _ _ φ x _`. Establish `e1` using `hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x) (spOver (EpsWeil.epsMap R D) ≫ V1)`. Rewrite `e1` using `[← ptV_eq]`. Establish `hX : spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x = spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x)`. Rewrite using `[← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]`.

Establish `hV : spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 = spOver (EpsWeil.epsMap R D') ≫ V1`. Rewrite using `[← Category.assoc, spOver_comp, epsHom_comp_epsMap]`. Rewrite `e1` using `[hX, hV]`. Establish `c1` using `hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x) (sm_whole _)`. Establish `c2` using `hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)`.

Rewrite `c1` using `[epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord]`. Establish `c3` using `hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)`. Rewrite `c3` using `[epsHom_comp_epsMap]`. Establish `s1` using `congrArg TrivSqZeroExt.snd e1`. Establish `s2` using `congrArg TrivSqZeroExt.snd c1`.

Establish `s3` using `congrArg TrivSqZeroExt.snd c3`. Simplify using `only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom, AlgHom.coe_coe, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3`. Simplify using `only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add]`. Take the linear combination `-s1 - s2 - s3`.
-/
theorem cohom_sndPull_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) →
    ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  intro R _ A B _ _ f hf v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R (A ⊗ B) f hf
  have hc := (GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R (A ⊗ B) f).1
  let V1 : Pt (A ⊗ B) (DualNumber R) := CartesianMonoidalCategory.lift 1 v
  refine ⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
      (spOver (EpsWeil.epsMap R D) ≫ V1) +
      fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) +
      fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
    (spOver (EpsWeil.epsMap R D) ≫ V1)
  rw [← ptV_eq] at e1
  have hX : spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x =
      spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x) := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]
  have hV : spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 = spOver (EpsWeil.epsMap R D') ≫ V1 := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_epsMap]
  rw [hX, hV] at e1
  have c1 := hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x)
    (sm_whole _)
  have c2 := hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)
  rw [epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord] at c1
  have c3 := hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)
  rw [epsHom_comp_epsMap] at c3
  have s1 := congrArg TrivSqZeroExt.snd e1
  have s2 := congrArg TrivSqZeroExt.snd c1
  have s3 := congrArg TrivSqZeroExt.snd c3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom, AlgHom.coe_coe, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add]
  linear_combination -s1 - s2 - s3

end GlobalTheory.PtExt
