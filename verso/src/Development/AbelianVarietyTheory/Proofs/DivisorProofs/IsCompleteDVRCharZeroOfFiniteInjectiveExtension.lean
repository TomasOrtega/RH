import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R R' _ _ _ _ _ _ ρ hR hE`. Take `⟨hdvr, -, hc0⟩` from `hR`. Take `⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩` from `hE`. Use `letI : Algebra R R' := ρ.toAlgebra`. Use `haveI : Module.Finite R R' := hfin`.

Use `haveI : Algebra.IsIntegral R R' := inferInstance`. Use `haveI := hnoeth`. Use `haveI := hic`. Establish `hinj' : Function.Injective (algebraMap R R')` using `hinj`. Use `haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'`.

Use `haveI : IsDedekindDomain R' := { }`. Establish `hnf : ¬ IsField R'` using `fun h => IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)`. Establish `hdvr' : IsDiscreteValuationRing R'` using `((IsDiscreteValuationRing.TFAE R' hnf).out 0 2).2 (inferInstance : IsDedekindDomain R')`. Conclude with `⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩`.
-/
theorem cDvr_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  intro R R' _ _ _ _ _ _ ρ hR hE
  obtain ⟨hdvr, -, hc0⟩ := hR
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩ := hE
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI := hnoeth
  haveI := hic
  have hinj' : Function.Injective (algebraMap R R') := hinj
  haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'
  haveI : IsDedekindDomain R' := { }
  have hnf : ¬ IsField R' := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)
  have hdvr' : IsDiscreteValuationRing R' := ((IsDiscreteValuationRing.TFAE R' hnf).out 0 2).2 (inferInstance : IsDedekindDomain R')
  exact ⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩

end GlobalTheory.Mum
