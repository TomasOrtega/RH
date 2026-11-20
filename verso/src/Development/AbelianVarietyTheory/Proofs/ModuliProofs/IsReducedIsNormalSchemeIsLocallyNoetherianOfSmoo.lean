import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hy : (y.asIdeal : Ideal A).IsPrime` using `y.isPrime`. Set `_ : Algebra A ((Sp A).presheaf.stalk y)` to `StructureSheaf.stalkAlgebra A y`. Establish `: IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A)` using `StructureSheaf.IsLocalization.to_stalk A y`. Conclude with `isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A) ((Sp A).presheaf.stalk y)`.
-/
theorem isDomain_and_isIntegrallyClosed_stalk_Sp (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (y : Sp A) :
    IsDomain ((Sp A).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp A).presheaf.stalk y) := by
  have hy : (y.asIdeal : Ideal A).IsPrime := y.isPrime
  let _ : Algebra A ((Sp A).presheaf.stalk y) := StructureSheaf.stalkAlgebra A y
  have : IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A) :=
    StructureSheaf.IsLocalization.to_stalk A y
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A)
    ((Sp A).presheaf.stalk y)

/- English proof (translation)
Introduce `k _ X s hs`. Establish `: Smooth s` using `hs`. Establish `hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)` using `forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)`. Use `⟨?_, hN, ?_⟩` and prove the remaining obligations. Establish `: ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)` using `fun x => by`.

Use `(hN x).1` as an intermediate fact. Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk X`. Establish `: IsLocallyNoetherian (Sp k)` using `inferInstance`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian s`.
-/
theorem isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by
  intro k _ X s hs
  have : Smooth s := hs
  have hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)
  refine ⟨?_, hN, ?_⟩
  · have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hN x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  · have : IsLocallyNoetherian (Sp k) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian s

end GlobalTheory
