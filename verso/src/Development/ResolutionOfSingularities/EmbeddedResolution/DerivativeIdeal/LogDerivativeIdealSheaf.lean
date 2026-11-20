import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealLocalization
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The section ring of the basic open is the localization at f, with the same action of the base ring after restriction. The section ideals of P and I on the basic open are extensions of their ideals on U. The section ring on U is Noetherian, so the ideal of P is finitely generated, and its module of differentials is finitely presented. The localization formula for logarithmic derivative ideals now identifies the extended ideal with the ideal assigned to the basic open.
-/
private theorem map_logDerivIdeal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)) =
        @logDerivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (P.ideal (X.affineBasicOpen f)) (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  have hUaff : IsAffineOpen U.1 := U.2
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have tower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have loc : IsLocalization.Away f Γ(X, X.basicOpen f) := hUaff.isLocalization_basicOpen f
  have fp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have noeth : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U rfl
  have hP : (P.ideal U).FG := IsNoetherian.noetherian _
  have key := logDerivIdeal_map_away (S' := Γ(X, X.basicOpen f)) k f hP (I.ideal U)
  rw [← P.map_ideal_basicOpen U f, ← I.map_ideal_basicOpen U f]
  exact key

noncomputable def logDerivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) : X.IdealSheafData where
  ideal U := @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)
  map_ideal_basicOpen := map_logDerivIdeal_basicOpen k p P I

/- English proof (authored)
On an affine open, the logarithmic derivative ideal sheaf is defined by applying the ring-level operation to the two section ideals, using the base algebra structure on the section ring.
-/
@[simp] theorem logDerivIdealSheaf_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) (U : X.affineOpens) :
    (logDerivIdealSheaf k p P I).ideal U =
      @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U) :=
  rfl

/- English proof (authored)
An inclusion of inputs gives an inclusion on every affine open. With P fixed, the ring-level logarithmic operation preserves each of those inclusions. This gives the inclusion of ideal sheaves.
-/
theorem logDerivIdealSheaf_mono (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (P : X.IdealSheafData) :
    Monotone (logDerivIdealSheaf k p P) := by
  intro I J h U
  exact @logDerivIdeal_le_logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U)
    (I.ideal U) (J.ideal U) (h U)

/- English proof (authored)
On each affine open the tangent derivations used for the logarithmic ideal are among all the derivations used for the ordinary derivative ideal. The latter contains the original ideal and all of the logarithmic generators, giving the inclusion.
-/
theorem logDerivIdealSheaf_le_derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    logDerivIdealSheaf k p P I ≤ derivIdealSheaf k p I := by
  intro U
  exact @logDerivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)

noncomputable def logDerivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) : ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I)

/- English proof (authored)
The zero-th iterate is the original ideal sheaf by definition.
-/
@[simp] theorem logDerivIdealSheafIterate_zero (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) : logDerivIdealSheafIterate k p P 0 I = I :=
  rfl

/- English proof (authored)
The recursive definition applies the logarithmic derivative ideal sheaf operation once more at a successor.
-/
theorem logDerivIdealSheafIterate_succ (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + 1) I =
      logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I) :=
  rfl

/- English proof (authored)
The first iterate applies the operation to the zero-th iterate, which is I.
-/
theorem logDerivIdealSheafIterate_one (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P 1 I = logDerivIdealSheaf k p P I :=
  rfl

/- English proof (authored)
Induct on r. At zero the outer iterate is the identity. At a successor apply one more logarithmic derivative step to both sides and use the recursive definition.
-/
theorem logDerivIdealSheafIterate_add (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r s : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + s) I =
      logDerivIdealSheafIterate k p P r (logDerivIdealSheafIterate k p P s I) := by
  induction r with
  | zero =>
      rw [Nat.zero_add, logDerivIdealSheafIterate_zero]
  | succ r ih =>
      have hrs : r + 1 + s = (r + s) + 1 := by omega
      rw [hrs, logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ, ih]

/- English proof (authored)
At zero both sides are the original section ideal. At a successor take the sections of the logarithmic derivative ideal sheaf of the preceding iterate. This applies the ring operation to the section ideal at the previous step, which is the preceding ring-level iterate by induction.
-/
@[simp] theorem logDerivIdealSheafIterate_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) (U : X.affineOpens) :
    (logDerivIdealSheafIterate k p P r I).ideal U =
      @logDerivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [logDerivIdealSheafIterate_zero,
        @logDerivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)]
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheaf_ideal, ih,
        @logDerivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U)]

/- English proof (authored)
The zero-th iterate is the identity and preserves inclusions. At each successor the logarithmic operation preserves the inclusion between the preceding iterates, so induction proves monotonicity.
-/
theorem logDerivIdealSheafIterate_mono (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) :
    Monotone (logDerivIdealSheafIterate k p P r) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealSheafIterate_zero, logDerivIdealSheafIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ]
      exact logDerivIdealSheaf_mono k p P (ih h)

/- English proof (authored)
At zero the two iterates agree. At a successor the logarithmic derivative sheaf of the previous logarithmic iterate lies in its ordinary derivative sheaf. By induction that ordinary derivative sheaf lies in the ordinary derivative sheaf of the preceding ordinary iterate, using monotonicity. This is the desired bound.
-/
theorem logDerivIdealSheafIterate_le_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P r I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero =>
      exact le_of_eq
        ((logDerivIdealSheafIterate_zero k p P I).trans (derivIdealSheafIterate_zero k p I).symm)
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
      exact le_trans
        (logDerivIdealSheaf_le_derivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I))
        (derivIdealSheaf_mono k p ih)

end FunctorialResolution.EmbeddedResolution
