import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.GenTrait

/- English proof (translation)
Establish `h1 : CharZero Γ(Z, ⊤)` using `RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom`. Establish `: Nonempty (⊤ : Z.Opens)` using `⟨⟨genericPoint Z, trivial⟩⟩`. Conclude with `charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)`.
-/
theorem charZero_functionField (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [CharZero W]
    (f : Sp W ⟶ Z) : CharZero Z.functionField := by
  have h1 : CharZero Γ(Z, ⊤) :=
    RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)

/- English proof (translation)
Introduce `Z _ W _ _ _ f`. Use `charZero_functionField Z W f` as an intermediate fact. Use `⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_, spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫ Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩` and prove the remaining obligations. Conclude with `⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩`. Rewrite using `[Scheme.Hom.comp_apply]`.

Establish `hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField` using `fun p => Subsingleton.elim _ _`. Conclude with `(congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans Scheme.fromSpecStalk_closedPoint`.
-/
theorem exists_trait_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  intro Z _ W _ _ _ f
  have := charZero_functionField Z W f
  refine ⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_,
    spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫
      Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩
  · exact ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      algebraRat.charZero _⟩
  · rw [Scheme.Hom.comp_apply]
    have hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField :=
      fun p => Subsingleton.elim _ _
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans
      Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GenTrait
