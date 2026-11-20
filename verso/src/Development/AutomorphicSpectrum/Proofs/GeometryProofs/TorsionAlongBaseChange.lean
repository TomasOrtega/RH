import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorBC

/- English proof (translation)
Substitute `h` using the available equality. Establish `e1 : y₁ = y₀` using `Over.OverMorphism.ext hy`. Establish `e2 : z₁ = z₀` using `Over.OverMorphism.ext hz`. Rewrite using `[e1, e2]`.
-/
private theorem mul_left_congr_of_base_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (y₀ z₀ : Over.mk f ⟶ G) (y₁ z₁ : Over.mk f' ⟶ G) (hy : y₁.left = y₀.left) (hz : z₁.left = z₀.left) :
    (y₁ * z₁).left = (y₀ * z₀).left := by
  subst h
  have e1 : y₁ = y₀ := Over.OverMorphism.ext hy
  have e2 : z₁ = z₀ := Over.OverMorphism.ext hz
  rw [e1, e2]

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : g₁ = g₀` using `Over.OverMorphism.ext hg`. Rewrite using `[e]`.
-/
private theorem pow_eq_one_congr_of_left_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (g₀ : Over.mk f ⟶ G) (g₁ : Over.mk f' ⟶ G) (hg : g₁.left = g₀.left) (N : ℕ) :
    g₁ ^ N = 1 ↔ g₀ ^ N = 1 := by
  subst h
  have e : g₁ = g₀ := Over.OverMorphism.ext hg
  rw [e]

/- English proof (translation)
Introduce `R _ _ T _ Γ S G _ x N i hT R' _ _ φ Γ' F hB`. Establish `hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ)` using `hB.cart.w`. Establish `hassoc : ∀ {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of R')), h ≫ (Spec.map (CommRingCat.ofHom φ) ≫ x) = (h ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x` using `fun _ => (Category.assoc _ _ _).symm`. Establish `lift1 : ∀ (Y : Over (Spec (CommRingCat.of R'))) (y : Y ⟶ Γ'.G), (y.left ≫ F) ≫ Γ.G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)`. Introduce `Y y`.

Rewrite using `[Category.assoc, hw, ← Category.assoc, Over.w y]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hT.isOver, ← Category.assoc, hw, Category.assoc]`. Introduce `Y y z y₀ z₀ hy hz`. Set `Y' : Over (Spec (CommRingCat.of R))` to `Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))`.

Set `y' : Y' ⟶ Γ.G` to `Over.homMk (y.left ≫ F) (lift1 Y y)`. Set `z' : Y' ⟶ Γ.G` to `Over.homMk (z.left ≫ F) (lift1 Y z)`. Set `y₁ : Over.mk (Y'.hom ≫ x) ⟶ G` to `Over.homMk y₀.left ((Over.w y₀).trans (hassoc Y.hom))`. Set `z₁ : Over.mk (Y'.hom ≫ x) ⟶ G` to `Over.homMk z₀.left ((Over.w z₀).trans (hassoc Y.hom))`. Establish `hm` using `hT.mul Y' y' z' y₁ z₁ (by show y₀.left = (y.left ≫ F) ≫ i; rw [Category.assoc]; exact hy) (by show z₀.left = (z.left ≫ F) ≫ i; rw [Category.assoc]; exact hz)`.

Establish `hF` using `hB.mul Y y z y' z' rfl rfl`. Rewrite using `[← mul_left_congr_of_base_eq (hassoc Y.hom) y₀ z₀ y₁ z₁ rfl rfl, hm, hF, Category.assoc]`. Introduce `Y y z h`. Set `Y' : Over (Spec (CommRingCat.of R))` to `Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))`. Establish `e` using `hT.inj Y' (Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G) (Over.homMk (z.left ≫ F) (lift1 Y z) : Y' ⟶ Γ.G) (by show (y.left ≫ F) ≫ i = (z.left ≫ F) ≫ i; rw [Category.assoc, Category.assoc]; exact h)`.

Establish `e2 : y.left ≫ F = z.left ≫ F` using `congrArg (fun m => m.left) e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `hB.cart.hom_ext e2 ((Over.w y).trans (Over.w z).symm)`. Introduce `Y g`. Set `Y' : Over (Spec (CommRingCat.of R))` to `Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))`.

Set `g₁ : Over.mk (Y'.hom ≫ x) ⟶ G` to `Over.homMk g.left ((Over.w g).trans (hassoc Y.hom))`. Rewrite using `[← pow_eq_one_congr_of_left_eq (hassoc Y.hom) g g₁ rfl N, hT.kernel Y' g₁]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', hy'⟩`. Use `⟨Over.homMk (hB.cart.lift y'.left Y.hom (Over.w y')) (hB.cart.lift_snd _ _ _), ?_⟩` and prove the remaining obligations.

Use `show hB.cart.lift y'.left Y.hom (Over.w y') ≫ F ≫ i = g.left`. Rewrite using `[← Category.assoc, hB.cart.lift_fst]`. Conclude with `hy'`. Introduce and unpack `⟨y, hy⟩`. Use `⟨(Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G), ?_⟩` and prove the remaining obligations.

Use `show (y.left ≫ F) ≫ i = g.left`. Rewrite using `[Category.assoc]`. Conclude with `hy`.
-/
theorem isTorsionAlong_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  intro R _ _ T _ Γ S G _ x N i hT R' _ _ φ Γ' F hB
  have hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ) := hB.cart.w
  have hassoc : ∀ {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of R')),
      h ≫ (Spec.map (CommRingCat.ofHom φ) ≫ x) = (h ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x :=
    fun _ => (Category.assoc _ _ _).symm
  have lift1 : ∀ (Y : Over (Spec (CommRingCat.of R'))) (y : Y ⟶ Γ'.G),
      (y.left ≫ F) ≫ Γ.G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro Y y
    rw [Category.assoc, hw, ← Category.assoc, Over.w y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hT.isOver, ← Category.assoc, hw, Category.assoc]
  · intro Y y z y₀ z₀ hy hz
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let y' : Y' ⟶ Γ.G := Over.homMk (y.left ≫ F) (lift1 Y y)
    let z' : Y' ⟶ Γ.G := Over.homMk (z.left ≫ F) (lift1 Y z)
    let y₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk y₀.left ((Over.w y₀).trans (hassoc Y.hom))
    let z₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk z₀.left ((Over.w z₀).trans (hassoc Y.hom))
    have hm := hT.mul Y' y' z' y₁ z₁
      (by show y₀.left = (y.left ≫ F) ≫ i; rw [Category.assoc]; exact hy)
      (by show z₀.left = (z.left ≫ F) ≫ i; rw [Category.assoc]; exact hz)
    have hF := hB.mul Y y z y' z' rfl rfl
    rw [← mul_left_congr_of_base_eq (hassoc Y.hom) y₀ z₀ y₁ z₁ rfl rfl, hm, hF, Category.assoc]
  · intro Y y z h
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    have e := hT.inj Y' (Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G)
      (Over.homMk (z.left ≫ F) (lift1 Y z) : Y' ⟶ Γ.G)
      (by show (y.left ≫ F) ≫ i = (z.left ≫ F) ≫ i; rw [Category.assoc, Category.assoc]; exact h)
    have e2 : y.left ≫ F = z.left ≫ F := congrArg (fun m => m.left) e
    apply Over.OverMorphism.ext
    exact hB.cart.hom_ext e2 ((Over.w y).trans (Over.w z).symm)
  · intro Y g
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let g₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g.left ((Over.w g).trans (hassoc Y.hom))
    rw [← pow_eq_one_congr_of_left_eq (hassoc Y.hom) g g₁ rfl N, hT.kernel Y' g₁]
    constructor
    · rintro ⟨y', hy'⟩
      refine ⟨Over.homMk (hB.cart.lift y'.left Y.hom (Over.w y')) (hB.cart.lift_snd _ _ _), ?_⟩
      show hB.cart.lift y'.left Y.hom (Over.w y') ≫ F ≫ i = g.left
      rw [← Category.assoc, hB.cart.lift_fst]
      exact hy'
    · rintro ⟨y, hy⟩
      refine ⟨(Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G), ?_⟩
      show (y.left ≫ F) ≫ i = g.left
      rw [Category.assoc]
      exact hy

end GlobalTheory.CompanionTheory.Ar.TorBC
