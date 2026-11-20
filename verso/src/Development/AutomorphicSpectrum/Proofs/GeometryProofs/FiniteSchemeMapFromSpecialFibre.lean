import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.CompanionTheory.FinFlatModel

open IsLocalRing

section Model

variable {R : Type} [CommRing R] [IsLocalRing R]

noncomputable def quotEquiv : (R ⧸ maximalIdeal R ^ (0 + 1)) ≃+* ResidueField R :=
  Ideal.quotEquivOfEq (by simp)

noncomputable def specIso :
    Spec (CommRingCat.of (ResidueField R)) ≅
      Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) where
  hom := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).toRingHom.comp (quotEquiv (R := R)).symm.toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).symm.toRingHom.comp (quotEquiv (R := R)).toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _

/- English proof (translation)
Simplify using `only [specIso, thick]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`.
-/
theorem specIso_hom_thick :
    (specIso (R := R)).hom ≫ thick R (maximalIdeal R) 0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) := by
  simp only [specIso, thick]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/- English proof (translation)
Use `IsPullback.of_iso (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R (ResidueField R) P)).flip (Iso.refl _) i.symm specIso (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `[hi]`. Simplify using `[specIso_hom_thick]`.
-/
theorem isPullback_fibre {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
        i.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (specIso (R := R)).hom)
      X.hom (thick R (maximalIdeal R) 0) := by
  refine IsPullback.of_iso
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R (ResidueField R) P)).flip
    (Iso.refl _) i.symm specIso (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [hi]
  · simp [specIso_hom_thick]

/- English proof (translation)
Take `⟨g, hg⟩` from `Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)`. Set `_ : Algebra R Γ(X.left, ⊤)` to `g.hom.toAlgebra`. Use `⟨Γ(X.left, ⊤), inferInstance, g.hom.toAlgebra, X.left.isoSpec, ?_⟩` and prove the remaining obligations. Establish `: CommRingCat.ofHom (algebraMap R Γ(X.left, ⊤)) = g` using `rfl`. Use `erw [this, hg]`.

Simplify using the standard rewrite rules.
-/
theorem exists_model (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    ∃ (P : Type) (_ : CommRing P) (_ : Algebra R P) (i : X.left ≅ Spec (CommRingCat.of P)),
      X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let _ : Algebra R Γ(X.left, ⊤) := g.hom.toAlgebra
  refine ⟨Γ(X.left, ⊤), inferInstance, g.hom.toAlgebra, X.left.isoSpec, ?_⟩
  have : CommRingCat.ofHom (algebraMap R Γ(X.left, ⊤)) = g := rfl
  erw [this, hg]
  simp

/- English proof (translation)
Establish `e1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R` using `R) (A := ResidueField R) (B := Q)).toRingHom) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Establish `e2 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R` using `R) (A := ResidueField R) (B := Q))) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ResidueField R) (B := P))) := by`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use extensionality with `x`. Simplify using the standard rewrite rules. Apply `pullback.hom_ext` to reduce the goal to its premises. Establish `h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫ pullback.fst Y.hom (thick R (maximalIdeal R) 0) = pullback.fst X.hom (thick R (maximalIdeal R) 0) ≫ f.left` using `pullback.lift_fst _ _ _`.

Rewrite using `[h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, reassoc_of% e1, ← (isPullback_fibre X i hi).isoPullback_inv_fst, hf]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`. Establish `h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫ pullback.snd Y.hom (thick R (maximalIdeal R) 0) = pullback.snd X.hom (thick R (maximalIdeal R) 0)` using `pullback.lift_snd _ _ _`. Rewrite using `[h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, reassoc_of% e2, ← (isPullback_fibre X i hi).isoPullback_inv_snd]`.
-/
theorem map_left_eq {P Q : Type} [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (φ : Q →ₐ[R] P)
    (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)))
    (hj : Y.hom = j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)))
    (hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv) :
    ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left =
      (isPullback_fibre X i hi).isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
        (isPullback_fibre Y j hj).isoPullback.hom := by
  have e1 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := Q)).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := Q))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := P))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp
  apply pullback.hom_ext
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.fst Y.hom (thick R (maximalIdeal R) 0) =
        pullback.fst X.hom (thick R (maximalIdeal R) 0) ≫ f.left := pullback.lift_fst _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst,
      reassoc_of% e1, ← (isPullback_fibre X i hi).isoPullback_inv_fst, hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.snd Y.hom (thick R (maximalIdeal R) 0) =
        pullback.snd X.hom (thick R (maximalIdeal R) 0) := pullback.lift_snd _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      reassoc_of% e2, ← (isPullback_fibre X i hi).isoPullback_inv_snd]

/- English proof (translation)
Establish `h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom` using `by simp [hi]`. Establish `h' : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R P)))`. Rewrite using `[h]`. Use `infer_instance`. Conclude with `RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h')`.
-/
theorem finite_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Finite R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h')

/- English proof (translation)
Establish `h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom` using `by simp [hi]`. Establish `h' : Flat (Spec.map (CommRingCat.ofHom (algebraMap R P)))`. Rewrite using `[h]`. Use `infer_instance`. Conclude with `RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h')`.
-/
theorem flat_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (hX : Flat X.hom)
    (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Flat R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : Flat (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h')

end Model

/- English proof (translation)
Introduce `R _ _ X Y _ _ f`. Establish `: IsAffine X.left` using `isAffine_of_isAffineHom X.hom`. Establish `: IsAffine Y.left` using `isAffine_of_isAffineHom Y.hom`. Take `⟨P, _, _, i, hi⟩` from `exists_model X`. Take `⟨Q, _, _, j, hj⟩` from `exists_model Y`.

Take `⟨ψ, hψ⟩` from `Spec.map_surjective (i.inv ≫ f.left ≫ j.hom)`. Establish `hcomm : CommRingCat.ofHom (algebraMap R Q) ≫ ψ = CommRingCat.ofHom (algebraMap R P)`. Apply `Spec.map_injective` to reduce the goal to its premises. Establish `hw : f.left ≫ Y.hom = X.hom` using `Over.w f`. Rewrite using `[Spec.map_comp, hψ]`.

Establish `h1 : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom` using `by simp [hi]`. Establish `h2 : j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) = Y.hom` using `hj.symm`. Rewrite using `[h1, ← hw]`. Simplify using `only [Category.assoc, h2]`. Set `φ : Q →ₐ[R] P` to `{ ψ.hom with commutes' := fun r => by`.

Use `congrArg (fun g => g.hom r) hcomm` as an intermediate fact. Simplify using `using this }`. Establish `hφ : CommRingCat.ofHom φ.toRingHom = ψ` using `rfl`. Establish `hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv`. Rewrite using `[hφ, hψ]`.

Simplify using the standard rewrite rules. Use `⟨P, Q, inferInstance, inferInstance, inferInstance, inferInstance, φ, i, j, (isPullback_fibre X i hi).isoPullback.symm, (isPullback_fibre Y j hj).isoPullback.symm, finite_of_model X i hi, finite_of_model Y j hj, fun h => flat_of_model X h i hi, hf, ?_⟩` and prove the remaining obligations. Conclude with `map_left_eq f φ i j hi hj hf`.
-/
theorem exists_algHom_model :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  intro R _ _ X Y _ _ f
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨P, _, _, i, hi⟩ := exists_model X
  obtain ⟨Q, _, _, j, hj⟩ := exists_model Y
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.inv ≫ f.left ≫ j.hom)
  have hcomm : CommRingCat.ofHom (algebraMap R Q) ≫ ψ = CommRingCat.ofHom (algebraMap R P) := by
    apply Spec.map_injective
    have hw : f.left ≫ Y.hom = X.hom := Over.w f
    rw [Spec.map_comp, hψ]
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
    have h2 : j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) = Y.hom := hj.symm
    rw [h1, ← hw]
    simp only [Category.assoc, h2]
  let φ : Q →ₐ[R] P :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun g => g.hom r) hcomm
        simpa using this }
  have hφ : CommRingCat.ofHom φ.toRingHom = ψ := rfl
  have hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv := by
    rw [hφ, hψ]
    simp
  refine ⟨P, Q, inferInstance, inferInstance, inferInstance, inferInstance, φ, i, j,
    (isPullback_fibre X i hi).isoPullback.symm, (isPullback_fibre Y j hj).isoPullback.symm,
    finite_of_model X i hi, finite_of_model Y j hj, fun h => flat_of_model X h i hi, hf, ?_⟩
  exact map_left_eq f φ i j hi hj hf

end GlobalTheory.CompanionTheory.FinFlatModel
