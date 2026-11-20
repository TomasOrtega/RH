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

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isDerivBalanced_iff (I : X.IdealSheafData) (m : ℕ) :
    IsDerivBalanced k p I m ↔ ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  Iff.rfl

/- English proof (translation)
The claim follows from `h i hi`.
-/
theorem IsDerivBalanced.derivIdealSheafIterate_pow_le {I : X.IdealSheafData} {m : ℕ} (h : IsDerivBalanced k p I m)
    {i : ℕ} (hi : i < m) : derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  h i hi

/- English proof (translation)
The claim follows from `h`.
-/
theorem isDerivBalanced_of_pow_le {I : X.IdealSheafData} {m : ℕ}
    (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m :=
  h

/- English proof (translation)
Introduce `i hi`. Take `rfl : i = 0` from `Nat.lt_one_iff.mp hi`. Establish `h : derivIdealSheafIterate k p 0 I = I` using `derivIdealSheafIterate_zero k p I`. Conclude with `le_of_eq (by rw [h, Nat.sub_zero])`.
-/
theorem isDerivBalanced_one (I : X.IdealSheafData) : IsDerivBalanced k p I 1 := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  have h : derivIdealSheafIterate k p 0 I = I := derivIdealSheafIterate_zero k p I
  exact le_of_eq (by rw [h, Nat.sub_zero])

noncomputable def maxContactIdeal (I : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  derivIdealSheafIterate k p (m - 1) I

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem maxContactIdeal_eq_derivIdealSheafIterate (I : X.IdealSheafData) (m : ℕ) :
    maxContactIdeal k p I m = derivIdealSheafIterate k p (m - 1) I :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem maxContactIdeal_one (I : X.IdealSheafData) : maxContactIdeal k p I 1 = I :=
  rfl

/- English proof (translation)
The claim follows from `derivIdealSheafIterate_ideal k p (m - 1) I U`.
-/
theorem maxContactIdeal_ideal (I : X.IdealSheafData) (m : ℕ) (U : X.affineOpens) :
    (maxContactIdeal k p I m).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (m - 1) (I.ideal U) :=
  derivIdealSheafIterate_ideal k p (m - 1) I U

def IsMaxContactInvariant (I : X.IdealSheafData) (m : ℕ) : Prop :=
  maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I

/- English proof (translation)
The claim follows from `h`.
-/
theorem isMaxContactInvariant_of_mul_le {I : X.IdealSheafData} {m : ℕ}
    (h : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I) : IsMaxContactInvariant k p I m :=
  h

end FunctorialResolution.EmbeddedResolution
