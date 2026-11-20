import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `R R' _ _ _ B B' _ _ _ _ α h f hf hb`. Use `letI : Algebra B B' := α.toAlgebra`. Use `letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra`. Use `haveI : IsScalarTower R R' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`. Use `haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm`.

Set `g : B →ₗ[R] B'` to `(IsScalarTower.toAlgHom R B B').toLinearMap`. Establish `e1 : ⇑(g.liftBaseChange R') = ⇑(liftSemi f)`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x b => simp [g, hf]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Use `haveI : Algebra.IsPushout R R' B B' := ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange R') (e1 ▸ hb)) fun n ↦ by simp [g]⟩`. Establish `e2 : ∀ ω : Ω[B⁄R], h.m1 ω = KaehlerDifferential.map R R' B B' ω`.

Introduce `ω`. Establish `hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hω using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Rewrite using `[SemiHom.m1_D, KaehlerDifferential.map_D]`. Both sides reduce to the same expression. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `smul b x _ hx`. Rewrite using `[SemiHom.oneFormMap_smul_semilinear, hx, LinearMap.map_smul_of_tower]`. Conclude with `algebraMap_smul B' b _`. Establish `e3 : ⇑(liftSemi h.m1) = ⇑(KaehlerDifferential.tensorKaehlerEquivBase R R' B B')`.

Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x ω => rw [liftSemi_tmul, KaehlerDifferential.tensorKaehlerEquivBase_tmul, e2]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Rewrite using `[e3]`. Conclude with `(KaehlerDifferential.tensorKaehlerEquivBase R R' B B').bijective`.
-/
theorem kaehler_liftSemi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B') (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B'), (∀ b, f b = α b) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi h.m1) := by
  intro R R' _ _ _ B B' _ _ _ _ α h f hf hb
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  let g : B →ₗ[R] B' := (IsScalarTower.toAlgHom R B B').toLinearMap
  have e1 : ⇑(g.liftBaseChange R') = ⇑(liftSemi f) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [g, hf]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange R') (e1 ▸ hb)) fun n ↦ by simp [g]⟩
  have e2 : ∀ ω : Ω[B⁄R], h.m1 ω = KaehlerDifferential.map R R' B B' ω := by
    intro ω
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [SemiHom.m1_D, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul b x _ hx =>
      rw [SemiHom.oneFormMap_smul_semilinear, hx, LinearMap.map_smul_of_tower]
      exact algebraMap_smul B' b _
  have e3 : ⇑(liftSemi h.m1) = ⇑(KaehlerDifferential.tensorKaehlerEquivBase R R' B B') := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x ω => rw [liftSemi_tmul, KaehlerDifferential.tensorKaehlerEquivBase_tmul, e2]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [e3]
  exact (KaehlerDifferential.tensorKaehlerEquivBase R R' B B').bijective

end GlobalTheory
