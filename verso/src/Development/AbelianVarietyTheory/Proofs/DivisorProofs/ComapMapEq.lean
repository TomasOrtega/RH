import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USepTrait

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem sp_comp {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem comap_map_eq {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] (I : Ideal R) :
    (I.map f).comap f = I := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I

end GlobalTheory.USepTrait
