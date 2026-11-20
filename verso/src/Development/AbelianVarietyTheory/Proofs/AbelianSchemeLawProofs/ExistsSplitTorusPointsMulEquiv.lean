import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusPoints

open Rosenlicht

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]`.
-/
theorem ΓSpecIso_inv_comp_specMap {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem map_left_fst {T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

/- English proof (translation)
Set `F` to `Over.pullback (toZ S)`. Set `G` to `splitTorusAff ZU X`. Set `m : Z ⟶ F.obj (G ⊗ G)` to `lift (a : Z ⟶ F.obj G) (b : Z ⟶ F.obj G) ≫ Functor.LaxMonoidal.μ F G G`. Establish `key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom (toZ S)) ≫ g.left = (m ≫ F.map g).left ≫ torusFst S X`. Introduce `g`.

Rewrite using `[Category.assoc, ← map_left_fst, Over.comp_left]`. Conclude with `(Category.assoc _ _ _).symm`. Use `⟨m.left ≫ pullback.fst (G ⊗ G).hom (toZ S), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Use `congr 2`.

Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))`. Rewrite using `[key]`. Use `congr 2`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))`. Rewrite using `[key]`.

Use `congr 2`.
-/
theorem exists_mul_factor (a b : Z ⟶ splitTorus S X) :
    ∃ q : Z.left ⟶ (splitTorusAff ZU X ⊗ splitTorusAff ZU X).left,
      q ≫ (fst _ _ : _ ⟶ splitTorusAff ZU X).left = a.left ≫ torusFst S X ∧
      q ≫ (snd _ _ : _ ⟶ splitTorusAff ZU X).left = b.left ≫ torusFst S X ∧
      q ≫ μ[splitTorusAff ZU X].left = (a * b).left ≫ torusFst S X := by
  let F := Over.pullback (toZ S)
  let G := splitTorusAff ZU X
  let m : Z ⟶ F.obj (G ⊗ G) := lift (a : Z ⟶ F.obj G) (b : Z ⟶ F.obj G) ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom (toZ S)) ≫ g.left =
      (m ≫ F.map g).left ≫ torusFst S X := by
    intro g
    rw [Category.assoc, ← map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨m.left ≫ pullback.fst (G ⊗ G).hom (toZ S), ?_, ?_, ?_⟩
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  · rw [key]
    congr 2

/- English proof (translation)
Take `⟨q, h1, h2, h3⟩` from `exists_mul_factor a b`. Set `A` to `torusRing ZU X`. Set `p : Z.left ⟶ Spec (.of (A ⊗[ZU.{0}] A))` to `q ≫ (pullbackSpecIso ZU.{0} A A).hom`. Set `φ` to `(Scheme.ΓSpecIso (.of (A ⊗[ZU.{0}] A))).inv ≫ p.appTop`. Establish `e1 : coord a = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ φ`.

Rewrite using `[← ΓSpecIso_inv_comp_specMap, coord, ← h1]`. Use `congr 2`. Conclude with `(congrArg (q ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A).symm).trans (Category.assoc _ _ _).symm`. Establish `e2 : coord b = CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ZU.{0}] A ⊗[ZU.{0}] A).toRingHom ≫ φ`. Rewrite using `[← ΓSpecIso_inv_comp_specMap, coord, ← h2]`.

Use `congr 2`. Conclude with `(congrArg (q ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A).symm).trans (Category.assoc _ _ _).symm`. Establish `e3 : coord (a * b) = CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A) ≫ φ`. Rewrite using `[← ΓSpecIso_inv_comp_specMap, coord, ← h3]`. Use `congr 2`.

Rewrite using `[e1, e2, e3]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]`. Rewrite using `[← map_mul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `Coalgebra.comul (R := ULift.{0} ℤ) (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ)) = (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ) ⊗ₜ[ULift.{0} ℤ] (1 : AddMonoidAlgebra (ULift.{0} ℤ) X)) * ((1 : AddMonoidAlgebra (ULift.{0} ℤ) X) ⊗ₜ[ULift.{0} ℤ] AddMonoidAlgebra.single x (1 : ULift.{ …`.

Simplify using the standard rewrite rules.
-/
theorem coord_mul_single (a b : Z ⟶ splitTorus S X) (x : X) :
    (coord (a * b)).hom (AddMonoidAlgebra.single x 1) =
      (coord a).hom (AddMonoidAlgebra.single x 1) * (coord b).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨q, h1, h2, h3⟩ := exists_mul_factor a b
  let A := torusRing ZU X
  let p : Z.left ⟶ Spec (.of (A ⊗[ZU.{0}] A)) := q ≫ (pullbackSpecIso ZU.{0} A A).hom
  let φ := (Scheme.ΓSpecIso (.of (A ⊗[ZU.{0}] A))).inv ≫ p.appTop
  have e1 : coord a = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h1]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e2 : coord b = CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[ZU.{0}] A ⊗[ZU.{0}] A).toRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h2]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e3 : coord (a * b) = CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A) ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h3]
    congr 2
  rw [e1, e2, e3]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← map_mul]
  congr 1
  change Coalgebra.comul (R := ULift.{0} ℤ) (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ)) =
    (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ) ⊗ₜ[ULift.{0} ℤ] (1 : AddMonoidAlgebra (ULift.{0} ℤ) X)) *
    ((1 : AddMonoidAlgebra (ULift.{0} ℤ) X) ⊗ₜ[ULift.{0} ℤ] AddMonoidAlgebra.single x (1 : ULift.{0} ℤ))
  simp

/- English proof (translation)
Rewrite using `[TorusInj.charUnit_val, coord, Scheme.Hom.comp_appTop]`. Establish `: (TorusInj.tFst (S` using `S) X).appLE ⊤ ⊤ (TorusInj.tle _) = (torusFst S X).appTop := by`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem coord_single (t : Z ⟶ splitTorus S X) (x : X) :
    (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (charUnit S X x).val := by
  rw [TorusInj.charUnit_val, coord, Scheme.Hom.comp_appTop]
  have : (TorusInj.tFst (S := S) X).appLE ⊤ ⊤ (TorusInj.tle _) = (torusFst S X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this]
  rfl

noncomputable def toHom (t : Z ⟶ splitTorus S X) : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
  ((coord t).hom.toMonoidHom.comp (AddMonoidAlgebra.of (ULift.{0} ℤ) X)).toHomUnits

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toHom_val (t : Z ⟶ splitTorus S X) (x : X) :
    (toHom t (Multiplicative.ofAdd x)).val = (coord t).hom (AddMonoidAlgebra.single x 1) := rfl

/- English proof (translation)
Use `⟨Over.homMk (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Establish `: (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom (specULiftZIsTerminal.hom_ext _ _) : Z.left ⟶ (splitTorus S X).left) ≫ torusFst S X = Z.left.toSpecΓ ≫ Spec.map φ` using `pullback.lift_fst _ _ _`. Use `(congrArg (fun g => (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ Scheme.Hom.appTop g) this).trans ?_` and prove the remaining obligations. Rewrite using `[ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]`.
-/
theorem exists_coord_eq (φ : torusRing ZU X ⟶ Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, coord t = φ := by
  refine ⟨Over.homMk (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), ?_⟩
  have : (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _) : Z.left ⟶ (splitTorus S X).left) ≫ torusFst S X =
      Z.left.toSpecΓ ≫ Spec.map φ := pullback.lift_fst _ _ _
  refine (congrArg (fun g => (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ Scheme.Hom.appTop g)
    this).trans ?_
  rw [ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b h`. Apply `coord_injective` to reduce the goal to its premises. Use `ext1`. Use `ringHom_ext_ZU fun y => ?_` and prove the remaining obligations.

Rewrite using `[← toHom_val, ← toHom_val, h]`. Introduce `u`. Use `letI : Algebra (ULift.{0} ℤ) Γ(Z.left, ⊤) := ULift.algebra' ℤ _`. Take `⟨t, ht⟩` from `exists_coord_eq (Z := Z) (X := X) (CommRingCat.ofHom (AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)).toRingHom)`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(toHom t (Multiplicative.ofAdd x)).val = _`. Rewrite using `[toHom_val, ht]`. Express the relevant statement in the definitionally equal form `AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u) (AddMonoidAlgebra.single _ 1) = _`. Simplify using the standard rewrite rules.
-/
theorem toHom_bijective : Function.Bijective (toHom : (Z ⟶ splitTorus S X) → _) := by
  constructor
  · intro a b h
    apply coord_injective
    ext1
    refine ringHom_ext_ZU fun y => ?_
    rw [← toHom_val, ← toHom_val, h]
  · intro u
    letI : Algebra (ULift.{0} ℤ) Γ(Z.left, ⊤) := ULift.algebra' ℤ _
    obtain ⟨t, ht⟩ := exists_coord_eq (Z := Z) (X := X) (CommRingCat.ofHom
      (AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)).toRingHom)
    refine ⟨t, ?_⟩
    ext x
    change (toHom t (Multiplicative.ofAdd x)).val = _
    rw [toHom_val, ht]
    change AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)
      (AddMonoidAlgebra.single _ 1) = _
    simp

/- English proof (translation)
Use extensionality with `x`. Conclude with `coord_mul_single a b x`.
-/
theorem toHom_mul (a b : Z ⟶ splitTorus S X) : toHom (a * b) = toHom a * toHom b := by
  ext x
  exact coord_mul_single a b x

end SplitTorusPoints

noncomputable def splitTorusPointsEquiv (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S) :
    (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ) :=
  { Equiv.ofBijective _ SplitTorusPoints.toHom_bijective with
    map_mul' := SplitTorusPoints.toHom_mul }

/- English proof (translation)
The claim follows from `SplitTorusPoints.coord_single t χ`.
-/
theorem splitTorusPointsEquiv_val (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S)
    (t : Z ⟶ splitTorus S X) (χ : X) :
    (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val =
      t.left.appTop.hom (charUnit S X χ).val :=
  SplitTorusPoints.coord_single t χ

/- English proof (translation)
Introduce `S X _ Z` and use `⟨splitTorusPointsEquiv S X Z, splitTorusPointsEquiv_val S X Z⟩`.
-/
theorem exists_splitTorus_points_mulEquiv :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S),
      ∃ e : (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ),
        ∀ (t : Z ⟶ splitTorus S X) (χ : X),
          (e t (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val :=
  fun S X _ Z => ⟨splitTorusPointsEquiv S X Z, splitTorusPointsEquiv_val S X Z⟩

end GlobalTheory
