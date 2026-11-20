import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

/- English proof (translation)
Introduce `V _ X p _ _`. Set `B : CommRingCat.{0}` to `Γ(X, ⊤)`. Set `g : CommRingCat.of V ⟶ B` to `(Scheme.Spec.preimage (X.isoSpec.inv ≫ p)).unop`. Establish `hg : Spec.map g = X.isoSpec.inv ≫ p` using `Scheme.Spec.map_preimage _`. Establish `hpg : p = X.isoSpec.hom ≫ Spec.map g` using `by rw [hg, Iso.hom_inv_id_assoc]`.

Establish `hsg : Smooth (Spec.map g)` using `by rw [hg]; infer_instance`. Establish `hgs : g.hom.Smooth` using `(HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsg`. Set `_ : Algebra V B` to `g.hom.toAlgebra`. Establish `: Algebra.Smooth V B` using `hgs`. Take `⟨A₀, B₀, _, _, hA₀, hsm, ⟨ψe⟩⟩` from `Algebra.Smooth.exists_subalgebra_fg ℤ V B`.

Set `T : CommRingCat.{0}` to `CommRingCat.of (TensorProduct A₀ V B₀)`. Set `inl : CommRingCat.of V ⟶ T` to `CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom`. Set `inr : CommRingCat.of B₀ ⟶ T` to `CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A₀) (A := V)).toRingHom`. Set `jIso : T ≅ B` to `{ hom := CommRingCat.ofHom ψe.symm.toRingHom inv := CommRingCat.ofHom ψe.toRingHom hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.apply_symm_apply x) inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.symm_apply_apply x) }`. Establish `hj : inl ≫ jIso.hom = g`.

Use extensionality with `v`. Conclude with `ψe.symm.commutes v`. Establish `hpb` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A₀ V B₀)).flip`. Set `e : X ≅ Spec T` to `X.isoSpec ≪≫ Scheme.Spec.mapIso jIso.op`. Use `⟨A₀, inferInstance, algebraMap A₀ V, Spec (CommRingCat.of B₀), Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)), e.hom ≫ Spec.map inr, ?_, ?_, inferInstance, ?_⟩` and prove the remaining obligations.

Use `(Subalgebra.fg_iff_finiteType A₀).mp hA₀` and compare the differences between its conclusion and the goal. Conclude with `(HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hsm)`. Use `IsPullback.of_iso hpb e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]`. Rewrite using `[Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, hpg]`.

Express the relevant statement in the definitionally equal form `(X.isoSpec.hom ≫ Spec.map jIso.hom) ≫ Spec.map inl = _`. Rewrite using `[Category.assoc, ← Spec.map_comp, hj]`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`.
-/
theorem GlobalTheory.exists_finiteType_model_of_smooth_affine :
    ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by
  intro V _ X p _ _
  let B : CommRingCat.{0} := Γ(X, ⊤)
  let g : CommRingCat.of V ⟶ B := (Scheme.Spec.preimage (X.isoSpec.inv ≫ p)).unop
  have hg : Spec.map g = X.isoSpec.inv ≫ p := Scheme.Spec.map_preimage _
  have hpg : p = X.isoSpec.hom ≫ Spec.map g := by rw [hg, Iso.hom_inv_id_assoc]
  have hsg : Smooth (Spec.map g) := by rw [hg]; infer_instance
  have hgs : g.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsg
  let _ : Algebra V B := g.hom.toAlgebra
  have : Algebra.Smooth V B := hgs
  obtain ⟨A₀, B₀, _, _, hA₀, hsm, ⟨ψe⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ V B
  let T : CommRingCat.{0} := CommRingCat.of (TensorProduct A₀ V B₀)
  let inl : CommRingCat.of V ⟶ T := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of B₀ ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A₀) (A := V)).toRingHom
  let jIso : T ≅ B :=
    { hom := CommRingCat.ofHom ψe.symm.toRingHom
      inv := CommRingCat.ofHom ψe.toRingHom
      hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.apply_symm_apply x)
      inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.symm_apply_apply x) }
  have hj : inl ≫ jIso.hom = g := by
    ext v
    exact ψe.symm.commutes v
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ V B₀)).flip
  let e : X ≅ Spec T := X.isoSpec ≪≫ Scheme.Spec.mapIso jIso.op
  refine ⟨A₀, inferInstance, algebraMap A₀ V, Spec (CommRingCat.of B₀),
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)), e.hom ≫ Spec.map inr, ?_, ?_,
    inferInstance, ?_⟩
  · convert (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  · exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hsm)
  · refine IsPullback.of_iso hpb e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, hpg]
      change (X.isoSpec.hom ≫ Spec.map jIso.hom) ≫ Spec.map inl = _
      rw [Category.assoc, ← Spec.map_comp, hj]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
