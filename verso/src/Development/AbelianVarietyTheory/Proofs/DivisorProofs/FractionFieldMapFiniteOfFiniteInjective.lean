import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.Mum.GenDesc

/- English proof (translation)
Introduce `R R' _ _ _ _ ρ hρ hfin`. Use `letI : Algebra R R' := ρ.toAlgebra`. Use `haveI : Module.Finite R R' := hfin`. Establish `hinj : Function.Injective (algebraMap R R')` using `hρ`. Use `haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj`.

Use `letI : Algebra (FractionRing R) (FractionRing R') := FractionRing.liftAlgebra R (FractionRing R')`. Use `haveI : IsScalarTower R (FractionRing R) (FractionRing R') := FractionRing.isScalarTower_liftAlgebra R (FractionRing R')`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R)) (FractionRing R') := inferInstance`. Use `haveI : Module.Finite (FractionRing R) (FractionRing R') := Module.Finite.of_isLocalization R R' (nonZeroDivisors R)`. Establish `heq : fracMap ρ hρ = algebraMap (FractionRing R) (FractionRing R')`.

Use `IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[fracMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' (FractionRing R')]`. Both sides reduce to the same expression. Rewrite using `[heq]`.

Conclude with `RingHom.finite_algebraMap.mpr inferInstance`.
-/
theorem fracMap_finite : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  intro R R' _ _ _ _ ρ hρ hfin
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  have hinj : Function.Injective (algebraMap R R') := hρ
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  letI : Algebra (FractionRing R) (FractionRing R') := FractionRing.liftAlgebra R (FractionRing R')
  haveI : IsScalarTower R (FractionRing R) (FractionRing R') :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing R')
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R)) (FractionRing R') :=
    inferInstance
  haveI : Module.Finite (FractionRing R) (FractionRing R') :=
    Module.Finite.of_isLocalization R R' (nonZeroDivisors R)
  have heq : fracMap ρ hρ = algebraMap (FractionRing R) (FractionRing R') := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    rw [fracMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' (FractionRing R')]
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.Mum.GenDesc
