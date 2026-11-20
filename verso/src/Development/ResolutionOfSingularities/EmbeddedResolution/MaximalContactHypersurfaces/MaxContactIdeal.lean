import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

def IsDerivBalanced (I : X.IdealSheafData) (m : ℕ) : Prop :=
  ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)

/- English proof (authored)
Derivative balance is defined by the displayed comparison of ideal powers for every derivative order below the mark. Expanding the definition gives both directions.
-/
theorem isDerivBalanced_iff (I : X.IdealSheafData) (m : ℕ) :
    IsDerivBalanced k p I m ↔ ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  Iff.rfl

/- English proof (authored)
Apply the derivative-balance condition to the given index, using that it lies below the mark.
-/
theorem IsDerivBalanced.derivIdealSheafIterate_pow_le {I : X.IdealSheafData} {m : ℕ} (h : IsDerivBalanced k p I m)
    {i : ℕ} (hi : i < m) : derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  h i hi

/- English proof (authored)
The assumed inequalities are exactly those in the definition of derivative balance.
-/
theorem isDerivBalanced_of_pow_le {I : X.IdealSheafData} {m : ℕ}
    (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m :=
  h

/- English proof (authored)
The only nonnegative index below one is zero. Zero iterations leave the ideal unchanged, and both powers in the required inequality then have exponent one. The ideals are equal.
-/
theorem isDerivBalanced_one (I : X.IdealSheafData) : IsDerivBalanced k p I 1 := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  have h : derivIdealSheafIterate k p 0 I = I := derivIdealSheafIterate_zero k p I
  exact le_of_eq (by rw [h, Nat.sub_zero])

noncomputable def maxContactIdeal (I : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  derivIdealSheafIterate k p (m - 1) I

/- English proof (authored)
The maximal-contact ideal is defined by iterating the derivative ideal one fewer time than the mark, using truncated subtraction at zero. This is the stated identity.
-/
@[simp] theorem maxContactIdeal_eq_derivIdealSheafIterate (I : X.IdealSheafData) (m : ℕ) :
    maxContactIdeal k p I m = derivIdealSheafIterate k p (m - 1) I :=
  rfl

/- English proof (authored)
For mark one the defining derivative count is zero. Zero iterations leave the original ideal unchanged.
-/
theorem maxContactIdeal_one (I : X.IdealSheafData) : maxContactIdeal k p I 1 = I :=
  rfl

/- English proof (authored)
The maximal-contact ideal is the derivative iterate one below the mark. Evaluating a derivative iterate on an affine open gives the same iterate of the section ideal over the induced section algebra. Apply that evaluation formula.
-/
theorem maxContactIdeal_ideal (I : X.IdealSheafData) (m : ℕ) (U : X.affineOpens) :
    (maxContactIdeal k p I m).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (m - 1) (I.ideal U) :=
  derivIdealSheafIterate_ideal k p (m - 1) I U

def IsMaxContactInvariant (I : X.IdealSheafData) (m : ℕ) : Prop :=
  maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I

/- English proof (authored)
The definition of maximal-contact invariance is the stated containment of the product of the maximal-contact ideal and the first derivative ideal. Thus the given containment proves the property.
-/
theorem isMaxContactInvariant_of_mul_le {I : X.IdealSheafData} {m : ℕ}
    (h : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I) : IsMaxContactInvariant k p I m :=
  h

end FunctorialResolution.EmbeddedResolution
