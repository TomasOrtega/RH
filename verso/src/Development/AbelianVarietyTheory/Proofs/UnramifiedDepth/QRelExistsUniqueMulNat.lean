import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

/- English proof (translation)
Establish `A : ∀ {X Y : Over S} (a : X ⟶ Y), ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left` using `fun a => pullback.lift_fst _ _ _`. Set `z : Over.mk t ⟶ (Over.pullback f).obj (G ⊗ G)` to `lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G`. Establish `z₁ : z ≫ (Over.pullback f).map (fst G G) = x` using `by simp [z]`. Establish `z₂ : z ≫ (Over.pullback f).map (snd G G) = y` using `by simp [z]`. Establish `hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Use `show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left`. Rewrite using `[lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]`. Use `show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left`. Rewrite using `[lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]`.

Establish `hxy : x * y = z ≫ (Over.pullback f).map μ[G]`. Rewrite using `[Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]`. Rewrite using `[hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]`. Both sides reduce to the same expression.
-/
private theorem mul_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (x y : Over.mk t ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk r ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x₀ * y₀).left = (x * y).left ≫ pullback.fst G.hom f := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

/- English proof (translation)
Establish `: IsClosedImmersion (Out.thick R I k)` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `infer_instance`.
-/
private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/- English proof (translation)
Introduce `R _ _ I D k G _ _ c`. Establish `hm` using `mono_thick R I k`. Establish `hf : Mono (pullback.fst G.hom (Out.thick R I k))` using `inferInstance`. Use `⟨fun S _ _ hS => ?_, ?_⟩` and prove the remaining obligations. Set `t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))` to `Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))`.

Establish `ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S))`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression. Establish `hw : ∀ (z : sp (R₀` using `R) S ⟶ G) (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left), w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by`. Introduce `z w h`.

Rewrite using `[← cancel_mono (Out.thick R I k), ht]`. Establish `h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom` using `(pullback.condition (f := G.hom) (g := Out.thick R I k)).symm`. Rewrite using `[Category.assoc, h1, ← Category.assoc, h]`. Conclude with `Over.w z`. Use `⟨fun z => ?_, ?_⟩` and prove the remaining obligations.

Set `w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left` to `pullback.lift z.left t ((Over.w z).trans ht.symm)`. Establish `h1 : w ≫ (Out.fstG I k G).left = z.left` using `pullback.lift_fst _ _ _`. Establish `h2 : (w ≫ c.pG.left) ≫ D.P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap R S))`. Establish `h3 : c.pG.left ≫ D.P.A.hom = (Out.thickObj R I k G).hom ≫ Out.thick R I k` using `Over.w c.pG`. Rewrite using `[Category.assoc, h3, ← Category.assoc, hw z w h1, ht]`.

Use `⟨Over.homMk (w ≫ c.pG.left) h2, ⟨w, h1, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨w', a, b⟩`. Establish `e : w' = w` using `(cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (a.trans h1.symm)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← b, e]`.

Both sides reduce to the same expression. Introduce and unpack `z z' y y' ⟨w, a, b⟩ ⟨w', a', b'⟩`. Use `c.q_hom` as an intermediate fact. Set `x : Over.mk t ⟶ Out.thickObj R I k G` to `Over.homMk w (hw z w a)`. Set `x' : Over.mk t ⟶ Out.thickObj R I k G` to `Over.homMk w' (hw z' w' a')`.

Use `⟨(x * x').left, (mul_left_fst G (Out.thick R I k) x x' z z' a.symm a'.symm).symm, ?_⟩` and prove the remaining obligations. Establish `e` using `mul_left_fst D.P.A (Out.thick R I k) (x ≫ c.q) (x' ≫ c.q) y y' (b.symm.trans (Category.assoc _ _ _).symm) (b'.symm.trans (Category.assoc _ _ _).symm)`. Rewrite `e` using `[← MonObj.mul_comp]`. Conclude with `((Category.assoc _ _ _).symm.trans e.symm)`. Introduce and unpack `S _ _ S' _ _ φ z y ⟨w, a, b⟩`.

Use `⟨(spMap φ).left ≫ w, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) a)`. Conclude with `(Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) b)`.
-/
theorem qRel_existsUnique_mul_nat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ z, ∃! y, QRel c S z y) ∧ ∀ z z' y y', QRel c S z y → QRel c S z' y' → QRel c S (z * z') (y * y')) ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') z y, QRel c S z y → QRel c S' (spMap φ ≫ z) (spMap φ ≫ y) := by
  intro R _ _ I D k G _ _ c
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst G.hom (Out.thick R I k)) := inferInstance
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
    have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hw : ∀ (z : sp (R₀ := R) S ⟶ G) (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
        w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
      intro z w h
      rw [← cancel_mono (Out.thick R I k), ht]
      have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
        (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
      rw [Category.assoc, h1, ← Category.assoc, h]
      exact Over.w z
    refine ⟨fun z => ?_, ?_⟩
    · let w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left :=
        pullback.lift z.left t ((Over.w z).trans ht.symm)
      have h1 : w ≫ (Out.fstG I k G).left = z.left := pullback.lift_fst _ _ _
      have h2 : (w ≫ c.pG.left) ≫ D.P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
        have h3 : c.pG.left ≫ D.P.A.hom = (Out.thickObj R I k G).hom ≫ Out.thick R I k := Over.w c.pG
        rw [Category.assoc, h3, ← Category.assoc, hw z w h1, ht]
      refine ⟨Over.homMk (w ≫ c.pG.left) h2, ⟨w, h1, rfl⟩, ?_⟩
      rintro y ⟨w', a, b⟩
      have e : w' = w := (cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (a.trans h1.symm)
      apply Over.OverMorphism.ext
      rw [← b, e]
      rfl
    · rintro z z' y y' ⟨w, a, b⟩ ⟨w', a', b'⟩
      have := c.q_hom
      let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw z w a)
      let x' : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w' (hw z' w' a')
      refine ⟨(x * x').left, (mul_left_fst G (Out.thick R I k) x x' z z' a.symm a'.symm).symm, ?_⟩
      have e := mul_left_fst D.P.A (Out.thick R I k) (x ≫ c.q) (x' ≫ c.q) y y'
        (b.symm.trans (Category.assoc _ _ _).symm) (b'.symm.trans (Category.assoc _ _ _).symm)
      rw [← MonObj.mul_comp] at e
      exact ((Category.assoc _ _ _).symm.trans e.symm)
  · rintro S _ _ S' _ _ φ z y ⟨w, a, b⟩
    refine ⟨(spMap φ).left ≫ w, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) a)
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) b)

end GlobalTheory.ChF
