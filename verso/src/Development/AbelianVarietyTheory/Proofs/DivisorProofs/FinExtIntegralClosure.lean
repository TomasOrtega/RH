import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Mum

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

abbrev baseMap (R : Type) [CommRing R] [IsDomain R] (E : Type) [Field E] [Algebra (FractionRing R) E] : R →+* E :=
  (algebraMap (FractionRing R) E).comp (algebraMap R (FractionRing R))

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

/- English proof (translation)
Use `letI := (baseMap R E).toAlgebra`. Use `haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl`. Take `⟨⟨hN, -, hI, hC⟩, -⟩` from `hR`. Use `set R₂ := integralClosure R E`. Use `haveI : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) E R₂`.

Use `haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_isAdicComplete R`. Use `haveI : IsLocalRing R₂ := GlobalTheory.TameKummer.isLocalRing_of_finite R R₂`. Use `⟨inferInstance, ⟨IsNoetherianRing.of_finite R R₂, inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R), GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Use `congrArg (algebraMap R₂ E) h` as an intermediate fact.

Conclude with `IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) E).injective this)`. Conclude with `RingHom.finite_algebraMap.2 inferInstance`.
-/
theorem finExt_integralClosure [IsLocalRing R] (hR : Base R) [FiniteDimensional (FractionRing R) E]
    [IsGalois (FractionRing R) E] :
    letI := (baseMap R E).toAlgebra
    ∃ _ : IsLocalRing (integralClosure R E), FinExt (algebraMap R (integralClosure R E)) := by
  letI := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨⟨hN, -, hI, hC⟩, -⟩ := hR
  set R₂ := integralClosure R E
  haveI : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) E R₂
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_isAdicComplete R
  haveI : IsLocalRing R₂ := GlobalTheory.TameKummer.isLocalRing_of_finite R R₂
  refine ⟨inferInstance, ⟨IsNoetherianRing.of_finite R R₂, inferInstance,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, ?_, ?_⟩
  · intro a b h
    have := congrArg (algebraMap R₂ E) h
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) E).injective this)
  · exact RingHom.finite_algebraMap.2 inferInstance

end GlobalTheory.GalClosure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

end GlobalTheory.GalClosure
