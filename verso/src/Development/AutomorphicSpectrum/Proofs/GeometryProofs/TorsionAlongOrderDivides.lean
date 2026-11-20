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
namespace GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled

/- English proof (translation)
Introduce `R _ _ T _ Γ S G _ x N i h t`. Set `lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G)` to `fun y => Over.homMk (y.left ≫ i) (by`. Establish `w` using `Over.w y`. Simplify using `only [Over.mk_hom, Category.assoc, h.isOver]`. Rewrite using `[← Category.assoc, w]`.

Use the proof step `rfl)`. Establish `lift_left : ∀ y, (lift y).left = y.left ≫ i` using `fun y => rfl`. Establish `lift_mul : ∀ y z, lift (y * z) = lift y * lift z` using `fun y z => by ext1`. Rewrite using `[h.mul (genPt R) y z (lift y) (lift z) rfl rfl]`. Both sides reduce to the same expression.

Establish `lift_one : lift 1 = 1`. Establish `e : lift 1 * lift 1 = lift 1` using `by rw [← lift_mul, _root_.mul_one]`. Conclude with `mul_eq_left.mp e`. Set `L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G)` to `{ toFun := lift, map_one' := lift_one, map_mul' := lift_mul }`. Establish `hk : lift (Γ.pt t) ^ N = 1` using `(h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩`.

Establish `hL : L (Γ.pt t ^ N) = L 1`. Rewrite using `[map_pow, map_one]`. Conclude with `hk`. Establish `hy : Γ.pt t ^ N = 1` using `h.inj (genPt R) _ _ (by`. Use `congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL` as an intermediate fact.

Conclude with `this)`. Establish `hp : Γ.pt (t ^ N) = Γ.pt 1` using `by rw [map_pow, map_one, hy]`. Set `c : Spec (CommRingCat.of (FractionRing R))` to `IsLocalRing.closedPoint (FractionRing R)`. Conclude with `Γ.pt_inj (t ^ N) 1 c c (by rw [hp])`.
-/
theorem pow_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  intro R _ _ T _ Γ S G _ x N i h t
  let lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun y =>
    Over.homMk (y.left ≫ i) (by
      have w := Over.w y
      simp only [Over.mk_hom, Category.assoc, h.isOver]
      rw [← Category.assoc, w]
      rfl)
  have lift_left : ∀ y, (lift y).left = y.left ≫ i := fun y => rfl
  have lift_mul : ∀ y z, lift (y * z) = lift y * lift z := fun y z => by
    ext1
    rw [h.mul (genPt R) y z (lift y) (lift z) rfl rfl]
    rfl
  have lift_one : lift 1 = 1 := by
    have e : lift 1 * lift 1 = lift 1 := by rw [← lift_mul, _root_.mul_one]
    exact mul_eq_left.mp e
  let L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) :=
    { toFun := lift, map_one' := lift_one, map_mul' := lift_mul }
  have hk : lift (Γ.pt t) ^ N = 1 := (h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩
  have hL : L (Γ.pt t ^ N) = L 1 := by
    rw [map_pow, map_one]
    exact hk
  have hy : Γ.pt t ^ N = 1 := h.inj (genPt R) _ _ (by
    have := congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL
    exact this)
  have hp : Γ.pt (t ^ N) = Γ.pt 1 := by rw [map_pow, map_one, hy]
  let c : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  exact Γ.pt_inj (t ^ N) 1 c c (by rw [hp])

end GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled
