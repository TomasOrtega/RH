import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivPush

/- English proof (translation)
Introduce `S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a`. Set `T : Over S` to `𝟙_ (Over S)`. Set `U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀)` to `toUnit _`. Establish `hU : U.left = f`. Simplify using `[U, T, Over.toUnit_left]`.

Set `cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])`. Establish `hca : c a = ∏ i, c (Pi.single i 1) ^ a i`. Establish `e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `congrArg cH e` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [map_zsmul] at this`. Conclude with `congrArg Additive.toMul this`. Establish `hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1))`.

Introduce `i`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left`. Rewrite using `[hU]`. Conclude with `hd i`.

Establish `key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a)`. Rewrite using `[hca, map_prod, map_prod]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]`. Use `congrArg (fun z => z.left) key` as an intermediate fact.

Rewrite using `[← hU]`. Conclude with `this`.
-/
theorem push_div_pts : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  intro S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a
  let T : Over S := 𝟙_ (Over S)
  let U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = f := by
    simp [U, T, Over.toUnit_left]
  let cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])
  have hca : c a = ∏ i, c (Pi.single i 1) ^ a i := by
    have e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg cH e
    rw [map_sum] at this
    simp only [map_zsmul] at this
    exact congrArg Additive.toMul this
  have hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1)) := by
    intro i
    apply Over.OverMorphism.ext
    show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left
    rw [hU]; exact hd i
  have key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a) := by
    rw [hca, map_prod, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]
  have := congrArg (fun z => z.left) key
  rw [← hU]
  exact this

end GlobalTheory.DivPush
