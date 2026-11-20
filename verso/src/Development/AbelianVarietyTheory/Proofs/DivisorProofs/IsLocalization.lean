import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def ker (σ : K →ₐ[ℂ] κ') : Ideal (K ⊗[ℂ] κ') :=
  RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))

instance ker_isPrime (σ : K →ₐ[ℂ] κ') : (ker σ).IsPrime := RingHom.ker_isPrime _

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_ker (σ : K →ₐ[ℂ] κ') (a : K ⊗[ℂ] κ') :
    a ∈ ker σ ↔ Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') a = 0 := Iff.rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem primeCompl_le (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (σ : K →ₐ[ℂ] κ') :
    (ker σ).primeCompl ≤ nonZeroDivisors (K ⊗[ℂ] κ') := by
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective _ L)
  intro a ha
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rintro rfl
  exact ha (Ideal.zero_mem _)

variable (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]

def loc (σ : K →ₐ[ℂ] κ') : Subring L :=
  (Localization.subalgebra.ofField L (ker σ).primeCompl (primeCompl_le L σ)).toSubring

def toLoc (σ : K →ₐ[ℂ] κ') : K ⊗[ℂ] κ' →+* loc L σ :=
  (algebraMap (K ⊗[ℂ] κ') L).codRestrict (loc L σ) fun a =>
    (Localization.subalgebra.ofField L (ker σ).primeCompl (primeCompl_le L σ)).algebraMap_mem a

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_toLoc (σ : K →ₐ[ℂ] κ') (a : K ⊗[ℂ] κ') :
    (toLoc L σ a : L) = algebraMap (K ⊗[ℂ] κ') L a := rfl

instance (σ : K →ₐ[ℂ] κ') : Algebra (K ⊗[ℂ] κ') (loc L σ) := (toLoc L σ).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_loc (σ : K →ₐ[ℂ] κ') :
    algebraMap (K ⊗[ℂ] κ') (loc L σ) = toLoc L σ := rfl

instance isLocalization (σ : K →ₐ[ℂ] κ') : IsLocalization.AtPrime (loc L σ) (ker σ) := by
  have h := Localization.subalgebra.isLocalization_ofField L (ker σ).primeCompl (primeCompl_le L σ)
  let S := Localization.subalgebra.ofField L (ker σ).primeCompl (primeCompl_le L σ)
  let e : S ≃ₐ[K ⊗[ℂ] κ'] loc L σ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (ker σ).primeCompl e

instance isLocalRing (σ : K →ₐ[ℂ] κ') : IsLocalRing (loc L σ) :=
  IsLocalization.AtPrime.isLocalRing (loc L σ) (ker σ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem map_ker (σ : K →ₐ[ℂ] κ') :
    (ker σ).map (toLoc L σ) = IsLocalRing.maximalIdeal (loc L σ) :=
  IsLocalization.AtPrime.map_eq_maximalIdeal (ker σ) (loc L σ)

end GlobalTheory.DiagLoc
