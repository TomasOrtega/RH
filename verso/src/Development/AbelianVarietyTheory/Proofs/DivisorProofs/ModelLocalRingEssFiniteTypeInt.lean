import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

/- English proof (translation)
Introduce `o Ω _ _ _ hA M x`. Use `haveI : LocallyOfFiniteType M.s := M.lft`. Set `y : PrimeSpectrum o` to `M.s x`. Use `letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y`. Use `haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ := StructureSheaf.IsLocalization.to_stalk _ y`.

Set `φ` to `@algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A`. Establish `h₁ : (M.s.stalkMap x).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap M.s x`. Establish `h₂ : φ.EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)`. Use `haveI : Algebra.FiniteType ℤ o := hA.ft`. Establish `h₀ : (algebraMap ℤ o).EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 inferInstance`.

Establish `h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType` using `(RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType`. Establish `h` using `((h₀.comp h₂).comp h₁)`. Establish `h'` using `h.comp h₃`. Rewrite using `[← RingHom.essFiniteType_algebraMap]`. Use `h'` and compare the differences between its conclusion and the goal.

Conclude with `RingHom.ext_int _ _`.
-/
theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
