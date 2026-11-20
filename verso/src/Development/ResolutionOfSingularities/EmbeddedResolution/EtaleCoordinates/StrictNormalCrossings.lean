import Mathlib
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev restrictIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    U.toScheme.IdealSheafData :=
  I.comap U.ι

/- English proof (authored)
The restriction of I to U is defined by pulling back I along the open immersion U → X. This is exactly the ideal on the right.
-/
theorem restrictIdeal_eq_comap_ι {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal I U = I.comap U.ι := rfl

/- English proof (authored)
An ideal sheaf is the unit ideal exactly when its support is empty. The support of the pullback to U is the inverse image of the support of I under U → X. A point of U is a point x of X with x ∈ U, and it belongs to that inverse image exactly when x belongs to the support of I. Thus the restricted ideal is the unit ideal exactly when every point of U avoids the support of I.
-/
theorem restrictIdeal_eq_top_iff_forall_notMem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) :
    restrictIdeal I U = ⊤ ↔ ∀ x : X, x ∈ U → x ∉ I.support := by
  have hbot : ((⊥ : TopologicalSpace.Closeds U.toScheme) : Set U.toScheme) = ∅ := rfl
  have hbot' : ∀ A : TopologicalSpace.Closeds U.toScheme,
      (A = ⊥ ↔ ∀ y : U.toScheme, y ∉ A) := by
    intro A
    constructor
    · rintro rfl y hy
      have hy' : y ∈ ((⊥ : TopologicalSpace.Closeds U.toScheme) : Set U.toScheme) := hy
      rw [hbot] at hy'
      exact hy'
    · intro hall
      have hA : (A : Set U.toScheme) = ∅ :=
        Set.Subset.antisymm (fun y hy => absurd hy (hall y)) (Set.empty_subset _)
      exact SetLike.coe_injective (hA.trans hbot.symm)
  have key : ∀ (x : X) (hx : x ∈ U),
      ((⟨x, hx⟩ : U.toScheme) ∈ (I.comap U.ι).support ↔ x ∈ I.support) := by
    intro x hx
    simp only [Scheme.IdealSheafData.support_comap]
    rfl
  rw [restrictIdeal_eq_comap_ι]
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, hbot']
  constructor
  · intro h x hx hmem
    exact h ⟨x, hx⟩ ((key x hx).mpr hmem)
  · rintro h ⟨x, hx⟩ hy
    exact h x hx ((key x hx).mp hy)

/- English proof (authored)
The inclusion V → X is the composite V → U → X. Pullback along this composite first restricts I to U and then pulls that restricted ideal back to V. This is also the direct restriction of I to V.
-/
theorem restrictIdeal_eq_comap_homOfLE_restrictIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) :
    restrictIdeal I V = (restrictIdeal I U).comap (X.homOfLE h) := by
  have hcomp : X.homOfLE h ≫ U.ι = V.ι := by simp
  show I.comap V.ι = (I.comap U.ι).comap (X.homOfLE h)
  rw [← Scheme.IdealSheafData.comap_comp, hcomp]

/- English proof (authored)
Express the two restrictions to V as pullbacks along V → U. Their inputs are the equal restrictions of I and J to U, so the pullbacks agree.
-/
theorem restrictIdeal_eq_of_le_of_eq {X : Scheme.{u}} {I J : X.IdealSheafData} {U V : X.Opens}
    (h : V ≤ U) (hU : restrictIdeal I U = restrictIdeal J U) :
    restrictIdeal I V = restrictIdeal J V := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal I h,
    restrictIdeal_eq_comap_homOfLE_restrictIdeal J h, hU]

/- English proof (authored)
Since f sends V into U, the two composites V → X → Y and V → U → Y agree, with V → U the restriction of f. Pullback of I along the first composite restricts the pullback along f. Pullback along the second composite pulls back the restriction of I to U. Functoriality identifies the two ideals.
-/
theorem restrictIdeal_comap_eq_comap_resLE_restrictIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    restrictIdeal (I.comap f) V = (restrictIdeal I U).comap (f.resLE U V h) := by
  have hcomp : f.resLE U V h ≫ U.ι = V.ι ≫ f := by simp
  show (I.comap f).comap V.ι = (I.comap U.ι).comap (f.resLE U V h)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]

abbrev zeroLocus {X : Scheme.{u}} (I : X.IdealSheafData) : TopologicalSpace.Closeds X :=
  I.support

/- English proof (authored)
The zero locus of an ideal sheaf is defined to be its support as a closed subset of X.
-/
theorem zeroLocus_eq_support {X : Scheme.{u}} (I : X.IdealSheafData) :
    zeroLocus I = I.support := rfl

def VanishesAlong {X : Scheme.{u}} (I J : X.IdealSheafData) : Prop := I ≤ J

/- English proof (authored)
Vanishing of I along J is defined to mean that I is contained in J. Both directions are the identity on this condition.
-/
theorem vanishesAlong_iff_le {X : Scheme.{u}} (I J : X.IdealSheafData) :
    VanishesAlong I J ↔ I ≤ J := Iff.rfl

def NonzeroOnComponents {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X)

/- English proof (authored)
The definition requires each irreducible component to have a point outside the support of I. This is precisely the stated condition that no component is contained in that support.
-/
theorem nonzeroOnComponents_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    NonzeroOnComponents I ↔ ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X) :=
  Iff.rfl

def IsSmoothDivisor {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) : Prop :=
  Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ AlgebraicGeometry.Smooth (D.subschemeι ≫ p)

/- English proof (authored)
The definition imposes two conditions. The ideal D is locally generated by a non-zero-divisor, and the subscheme cut out by D is smooth over the base via its inclusion followed by p. These are the two conditions on the right.
-/
theorem isSmoothDivisor_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) :
    IsSmoothDivisor p D ↔
      Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ AlgebraicGeometry.Smooth (D.subschemeι ≫ p) :=
  Iff.rfl

abbrev affineSpaceFin (k : Type u) [Field k] (m : ℕ) : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))

abbrev affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ⟶ Spec (CommRingCat.of k) :=
  (affineSpaceFin k m ↘ Spec (CommRingCat.of k))

structure EtaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) : Type u where
  map : U.toScheme ⟶ affineSpaceFin k m
  comp_struct : map ≫ affineSpaceFinToSpec k m = U.ι ≫ p
  isEtale : AlgebraicGeometry.Etale map

def coordSubspaceIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (affineSpaceFin k m).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span
      ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
        (S : Set (Fin m))))

/- English proof (authored)
Take the coordinate functions indexed by S in the coordinate ring of the affine space. The coordinate subspace ideal sheaf is defined by taking the sheaf associated to the ring ideal they generate, giving the displayed formula.
-/
theorem coordSubspaceIdeal_eq_ofIdealTop_span_coord (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span
          ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
            (S : Set (Fin m)))) := rfl

def EtaleChart.coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) : U.toScheme.IdealSheafData :=
  (coordSubspaceIdeal k m S).comap c.map

/- English proof (authored)
The chart ideal for S is defined by pulling back the coordinate subspace ideal for S along the chart's étale map.
-/
theorem EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) :
    c.coordIdeal S = (coordSubspaceIdeal k m S).comap c.map := rfl

def InStrictNormalCrossingPositionAt {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
    (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
    (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
    (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t})

def InStrictNormalCrossingPosition {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) : Prop :=
  (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x

/- English proof (authored)
By definition, the global condition consists of smoothness of each divisor in E and the local chart condition at every point of X. Unfolding it gives exactly the stated conjunction.
-/
theorem inStrictNormalCrossingPosition_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) :
    InStrictNormalCrossingPosition p E ↔
      (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x :=
  Iff.rfl

def HasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support,
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : Finset (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S

/- English proof (authored)
Unfold the condition at a point x of the support of Z. It asks for an étale coordinate chart around x and an assignment of optional coordinate indices to the entries of E. An unassigned entry restricts to the unit ideal, and an assigned entry restricts to the corresponding coordinate hyperplane ideal. Distinct assigned entries use distinct coordinates. In the same chart, Z restricts to the ideal of the coordinates indexed by S. These are exactly the witnesses and conditions on the right.
-/
theorem hasStrictNormalCrossingsWith_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    HasStrictNormalCrossingsWith p Z E ↔
      ∀ x ∈ Z.support,
        ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
          (S : Finset (Fin m)),
          (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
          (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
          (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
            restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
          restrictIdeal Z U = c.coordIdeal S :=
  Iff.rfl

/- English proof (authored)
Apply the defining local condition of h at the given point x of the support of Z. This supplies the chart, the assignment for E, and the coordinate set for Z with all the required properties.
-/
theorem HasStrictNormalCrossingsWith.exists_etaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {E : List X.IdealSheafData} (h : HasStrictNormalCrossingsWith p Z E) {x : X} (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : Finset (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S :=
  h x hx

/- English proof (authored)
For each x in the support of Z, the hypothesis supplies a chart with distinct coordinate indices for the assigned entries of E and the required coordinate ideal for Z. These pointwise data give the defining condition for strict normal crossings along Z.
-/
theorem hasStrictNormalCrossingsWith_of_forall_exists_etaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {E : List X.IdealSheafData}
    (h : ∀ x ∈ Z.support,
      ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
        (S : Finset (Fin m)),
        (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
        (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
        (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
          restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
        restrictIdeal Z U = c.coordIdeal S) :
    HasStrictNormalCrossingsWith p Z E :=
  h

/- English proof (authored)
Use the given neighbourhood, chart, and assignment in the definition at x. The three conditions in the hypothesis say that assigned indices are distinct and determine the restrictions of every assigned or unassigned entry of E.
-/
theorem inStrictNormalCrossingPositionAt_of_exists_etaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {E : List X.IdealSheafData} {x : X}
    (h : ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t})) :
    InStrictNormalCrossingPositionAt p E x :=
  h

/- English proof (authored)
Unfold the local condition at x. Its witnesses are the neighbourhood, chart, and coordinate assignment, and its three requirements give exactly the desired properties.
-/
theorem InStrictNormalCrossingPositionAt.exists_etaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {E : List X.IdealSheafData} {x : X}
    (h : InStrictNormalCrossingPositionAt p E x) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :=
  h

/- English proof (authored)
At x, choose the local chart, the coordinate set S for Z, and the assignment b for the full list H :: E. Keep the chart and S. Assign b(0) to H and b(i+1) to the i-th entry of E. The old ideal conditions at index 0 give the two possibilities for H. At index i+1 they give the two possibilities for the corresponding tail entry.

If a tail entry uses the coordinate assigned to H, injectivity on the assigned coordinates gives i+1 = 0, which is impossible. If two tail entries use the same coordinate, injectivity gives i+1 = j+1 and hence i = j. The original ideal condition for Z applies to the retained chart and S.
-/
theorem HasStrictNormalCrossingsWith.exists_etaleChart_of_cons {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {H : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z (H :: E)) {x : X} (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m))
      (aH : Option (Fin m)) (a : ℕ → Option (Fin m)),
      restrictIdeal Z U = c.coordIdeal S ∧
      (aH = none → restrictIdeal H U = ⊤) ∧
      (∀ t : Fin m, aH = some t → restrictIdeal H U = c.coordIdeal {t}) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      (∀ i < E.length, ∀ t : Fin m, a i = some t → aH ≠ some t) ∧
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) := by
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h x hx
  have hzero : 0 < (H :: E).length := by simp
  refine ⟨U, hU, m, c, S, a 0, fun i => a (i + 1), h4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have hres := h2 0 hzero h0
    simpa using hres
  · intro t ht
    have hres := h3 0 hzero t ht
    simpa using hres
  · intro i hi hni
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hres := h2 (i + 1) hi' hni
    simpa using hres
  · intro i hi t ht
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hres := h3 (i + 1) hi' t ht
    simpa using hres
  · intro i hi t ht hc
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have := h1 (i + 1) hi' 0 hzero t ht hc
    omega
  · intro i hi j hj t hti htj
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hj' : j + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have := h1 (i + 1) hi' (j + 1) hj' t hti htj
    omega

end FunctorialResolution.EmbeddedResolution
