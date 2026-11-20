import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GModStalk

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z z`. Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Take `⟨-, hft, -⟩` from `GlobalTheory.CoeffRings.coeff_isDedFrac E H l c`. Use `haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj`.

Use `haveI : Flat Z.s := Z.flat`. Set `y : PrimeSpectrum (𝓞 c.F)` to `Z.s z`. Use `letI : Algebra (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y`. Use `haveI : IsLocalization.AtPrime ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal := StructureSheaf.IsLocalization.to_stalk _ y`. Set `φ` to `algebraMap (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z))`.

Establish `h₁ : (Z.s.stalkMap z).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap Z.s z`. Establish `h₂ : φ.EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)`. Establish `hφ : Function.Injective φ` using `IsLocalization.injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `hσ : Function.Injective (Z.s.stalkMap z).hom`. Establish `h` using `Flat.stalkMap Z.s z`.

Use `algebraize [(Z.s.stalkMap z).hom]`. Establish `: IsLocalHom (algebraMap ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z))` using `Z.s.toLRSHom.prop z`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (B := Z.X.presheaf.stalk z)` as an intermediate fact. Conclude with `FaithfulSMul.algebraMap_injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)`. Use `⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩` and prove the remaining obligations.

Establish `hO : Algebra.EssFiniteType ℤ (𝓞 c.F)` using `inferInstance`. Use `RingHom.essFiniteType_algebraMap.1 ?_` and prove the remaining obligations. Use `(RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.
-/
theorem charZero_essFiniteType_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X),
    CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  intro E _ _ _ H D l Xo c Z z
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨-, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  haveI : Flat Z.s := Z.flat
  let y : PrimeSpectrum (𝓞 c.F) := Z.s z
  letI : Algebra (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
  have h₁ : (Z.s.stalkMap z).hom.EssFiniteType := LocallyOfFiniteType.stalkMap Z.s z
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have hσ : Function.Injective (Z.s.stalkMap z).hom := by
    have h := Flat.stalkMap Z.s z
    algebraize [(Z.s.stalkMap z).hom]
    have : IsLocalHom (algebraMap ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)) :=
      Z.s.toLRSHom.prop z
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
      (B := Z.X.presheaf.stalk z)
    exact FaithfulSMul.algebraMap_injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)
  refine ⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩
  have hO : Algebra.EssFiniteType ℤ (𝓞 c.F) := inferInstance
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

end GlobalTheory.GModStalk
