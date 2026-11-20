import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem GeomInt.baseChange {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    (K' : Type) [Field K'] [Algebra K K'] : GeomInt K' (K' ⊗[K] R) := by
  haveI := h.1
  refine ⟨inferInstance, fun L _ _ => ?_⟩
  letI : Algebra K L := ((algebraMap K' L).comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := h.2 L
  exact (Algebra.TensorProduct.cancelBaseChange K K' L L R).toMulEquiv.isDomain _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Equip the data with the indicated structure. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem GeomInt.away {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    {r : R} (hr : r ≠ 0) : GeomInt K (Localization.Away r) := by
  haveI := h.1
  haveI : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  refine ⟨Algebra.Smooth.comp K R _, fun L _ _ => ?_⟩
  haveI := h.2 L
  letI : Algebra (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    (Algebra.TensorProduct.map (AlgHom.id L L)
      (IsScalarTower.toAlgHom K R (Localization.Away r))).toAlgebra
  haveI : IsScalarTower L (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right K L (Submonoid.powers r)
    (Localization.Away r) (by ext; simp [RingHom.algebraMap_toAlgebra])
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (hM := ?_) (S := L ⊗[K] Localization.Away r)
    (M := (Submonoid.powers r).map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
  rw [Submonoid.map_powers]
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  exact fun h0 => hr (hinj (by rw [h0, map_zero]))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem geomInt_baseChange_and_away :
    ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R],
      GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) :=
  fun _ K' _ _ _ _ _ _ h => ⟨h.baseChange K', fun _ hr => h.away hr⟩

end GlobalTheory.KeyFam
