import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackOverField Y k' q g).boundary.length :=
  pullbackOverFieldIndex T Y k' q g

@[simp]
/- English proof (authored)
Pulling back the boundary preserves list positions. The new index has the same natural-number value as the original index.
-/
theorem pullbackIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackIndex T Y k' q g j : Fin (T.pullbackOverField Y k' q g).boundary.length) : ℕ) = (j : ℕ) :=
  pullbackOverFieldIndex_val T Y k' q g j

def pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin (T.pullbackOverField Y k' q g).boundary.length → Fin T.boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g)

@[simp]
/- English proof (authored)
The inverse index map uses equality of the boundary lengths to reinterpret an upper position in the lower list. Its natural-number value stays the same.
-/
theorem pullbackIndexSymm_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    ((pullbackIndexSymm T Y k' q g j : Fin T.boundary.length) : ℕ) = (j : ℕ) :=
  rfl

@[simp]
/- English proof (authored)
Both index maps preserve the numeric position. Their composite has the original numeric value and therefore equals the original finite index.
-/
theorem pullbackIndexSymm_pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    pullbackIndexSymm T Y k' q g (pullbackIndex T Y k' q g j) = j := by
  apply Fin.val_injective
  rw [pullbackIndexSymm_val, pullbackIndex_val]

@[simp]
/- English proof (authored)
Sending a pulled-back index downstairs and then upstairs leaves its numeric value fixed. Equality of these values identifies the original index with the result.
-/
theorem pullbackIndex_pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    pullbackIndex T Y k' q g (pullbackIndexSymm T Y k' q g j) = j := by
  apply Fin.val_injective
  rw [pullbackIndex_val, pullbackIndexSymm_val]

def pullbackAlongIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackAlong Y q g).boundary.length :=
  EmbeddedResolution.pullbackAlongIndex T Y q g

@[simp]
/- English proof (authored)
The comparison at the original base field uses the index map for pullback over that field. It keeps the numeric position in the list.
-/
theorem pullbackAlongIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackAlongIndex T Y q g j : Fin (T.pullbackAlong Y q g).boundary.length) : ℕ) = (j : ℕ) :=
  EmbeddedResolution.pullbackAlongIndex_val T Y q g j

structure IsComponentCompatiblePullback (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) : Prop where
  comapCenter : ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
    𝒞 ⊆ intersectionComponents T.boundary J →
    ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
      ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
          (Finset.image (pullbackIndex T Y k' q g) J)).subschemeι ⁻¹'
          ⋃₀ {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
        (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
          componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) J)
            {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop'
  componentsDown : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
      ∃ C ∈ intersectionComponents T.boundary J, Set.MapsTo (⇑g) C' C ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  componentsUp : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C ∈ intersectionComponents T.boundary J, ∀ y : ↥Y, g y ∈ C →
      ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
        y ∈ C' ∧
          ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  orderAtComap : ∀ (I : T.scheme.IdealSheafData) (y : ↥Y), orderAt (I.comap g) y = orderAt I (g y)

/- English proof (authored)
The weak comparison holds when the first invariant is strictly smaller or all its comparison entries coincide with those of the second. Substituting the minimum size, maximum order and sorted chosen indices into these entries gives the right-hand condition.
-/
theorem centerInvariant_le_iff {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)
    (I' : Y'.IdealSheafData) (m' : ℕ) (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Le (centerInvariant I' m' L') ↔
      ((centerInvariant I m L).Lt (centerInvariant I' m' L') ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧ maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
          sortedIndices (lexMaxIndices I m L) = sortedIndices (lexMaxIndices I' m' L'))) :=
  Iff.rfl

/- English proof (authored)
Since the upper minimum size is positive, choose an upper component attaining it. Send its selected indices to their counterparts in the lower boundary. This preserves cardinality and recovers the original selection after pulling back the indices. The component comparison gives a lower component whose generic point is the image of the upper generic point. Order preservation at that point gives the same order downstairs, so the lower component is a candidate of the same positive size. The lower minimum is therefore positive and at most the upper one.
-/
theorem minIndexCard_ne_zero_and_le_pullbackOverField (_hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (_hT : IsLocallyMonomialTriple T)
    (_hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      minIndexCard T.ideal T.mult T.boundary ≤
        minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary := by
  obtain ⟨J', C', hcard', hmem', hord'⟩ :=
    exists_isCandidateComponent_minIndexCard (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary h0
  have hinj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg (fun z : Fin T.boundary.length => (z : ℕ)) hab
    simpa using h
  have hJ : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rwa [pullbackIndex_pullbackIndexSymm]
    · intro hx
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g x,
        Finset.mem_image.2 ⟨x, hx, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g x⟩
  obtain ⟨C, hC, -, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C'
      (by rw [hJ]; exact hmem')
  have h4 : g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
      = (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmem')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have heq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    have e1 : orderAlong (T.pullbackOverField Y k' q g).ideal C'
        = orderAt (T.pullbackOverField Y k' q g).ideal
            (isIrreducible_of_mem_intersectionComponents hmem').genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hmem'
    have e2 : orderAt (T.pullbackOverField Y k' q g).ideal
          (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
        = orderAt T.ideal (g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint) :=
      hP.orderAtComap T.ideal _
    have e3 : orderAlong T.ideal C
        = orderAt T.ideal (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hC
    rw [e1, e2, h4, e3]
  have hord2 : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hx : (T.mult : ℕ∞) ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := hord'
    rw [heq] at hx
    exact hx
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card = J'.card :=
    Finset.card_image_of_injective J' hinj
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    ⟨hcardJ.trans hcard', hC, hord2⟩
  have hone : 1 ≤ minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary := Nat.pos_of_ne_zero h0
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C :=
    ⟨minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary, hone,
      Finset.image (pullbackIndexSymm T Y k' q g) J', C, hcand⟩
  have hspec := minIndexCard_spec T.ideal T.mult T.boundary hex
  refine ⟨?_, hspec.2.2 _ hone _ _ hcand⟩
  have h1 := hspec.1
  omega

/- English proof (authored)
The common minimum size is positive. Choose an upper component attaining the maximum order at that size. Send its indices downstairs without changing their number and use the component comparison to send its generic point to a lower component's generic point. Order preservation gives the same order there. This is a lower candidate at the common minimum size, so the lower maximum is at least its order, which is the upper maximum.
-/
theorem maxCandidateOrder_le_of_minIndexCard_eq (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by
    rw [hmin]
    exact h0
  obtain ⟨J', C', hcand', hord'⟩ := (maxCandidateOrder_spec hGeom hT' h0').1
  have hcandSplit :
      J'.card = minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary ∧
        C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary J' ∧
        ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
          orderAlong (T.pullbackOverField Y k' q g).ideal C' := hcand'
  obtain ⟨hcard', hmemC', hmult'⟩ := hcandSplit
  have hback_inj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg Fin.val hab
    rwa [pullbackIndexSymm_val, pullbackIndexSymm_val] at h
  have himg : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rw [pullbackIndex_pullbackIndexSymm]
      exact hb
    · intro hj
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g j⟩
  have hmem : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (Finset.image (pullbackIndexSymm T Y k' q g) J')) := by
    rw [himg]
    exact hmemC'
  obtain ⟨C, hC, _hmaps, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C' hmem
  have hg : g (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint =
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmemC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    rw [orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hmemC',
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, ← hg]
    exact hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hback_inj, hcard']
    exact hmin
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hb := hmult'
    rw [hord] at hb
    exact hb
  have hcandT : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    And.intro hcardJ (And.intro hC hmultC)
  have hmaxOrd := (maxCandidateOrder_spec hGeom hT h0).2.1 _ _ hcandT
  rw [← hord', hord]
  exact hmaxOrd

/- English proof (authored)
Expand the strict comparison of the invariant entries. A smaller minimum size gives the comparison first. At equal size a larger maximum order gives the comparison, and at equal order the increasing lists of chosen indices are compared lexicographically. These are the stated cases.
-/
private theorem centerInvariant_lt_iff_lex {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (I' : Y'.IdealSheafData) (m' : ℕ)
    (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Lt (centerInvariant I' m' L') ↔
      (minIndexCard I m L < minIndexCard I' m' L' ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧
          (maxCandidateOrder I' m' L' < maxCandidateOrder I m L ∨
            (maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
              List.Lex (· < ·) (sortedIndices (lexMaxIndices I m L))
                (sortedIndices (lexMaxIndices I' m' L')))))) :=
  Iff.rfl

/- English proof (authored)
Equal images under the inverse index map have equal numeric positions. The map preserves positions, so the two original upper indices have equal positions and are equal.
-/
private theorem pullbackIndexSymm_injective (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Function.Injective (pullbackIndexSymm T Y k' q g) := by
  intro a b h
  apply Fin.val_injective
  rw [← pullbackIndexSymm_val T Y k' q g a, ← pullbackIndexSymm_val T Y k' q g b, h]

/- English proof (authored)
The order on finite indices is the order of their numeric values. Since the pullback index map preserves these values, it preserves strict inequality.
-/
private theorem pullbackIndex_strictMono (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    StrictMono (pullbackIndex T Y k' q g) := by
  intro a b hab
  have h : (a : ℕ) < (b : ℕ) := Fin.lt_def.mp hab
  rw [Fin.lt_def, pullbackIndex_val, pullbackIndex_val]
  exact h

/- English proof (authored)
A strictly increasing map commutes with sorting the index set. Taking numeric positions after applying the pullback index map gives the same entries as taking them before, so the two sorted lists coincide.
-/
private theorem sortedIndices_image_pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (J : Finset (Fin T.boundary.length)) :
    sortedIndices (Finset.image (pullbackIndex T Y k' q g) J) = sortedIndices J := by
  rw [sortedIndices_image_of_strictMono (pullbackIndex T Y k' q g)
    (pullbackIndex_strictMono T Y k' q g) J]
  simp only [pullbackIndex_val]
  rfl

/- English proof (authored)
Order along each component is order at its generic point. By the generic-point comparison, the upper generic point maps to the lower one. The assumed preservation of order under pullback equates these two values.
-/
private theorem orderAlong_pullbackOverField_eq_orderAlong (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (hP : IsComponentCompatiblePullback T Y k' q g) (J : Finset (Fin T.boundary.length))
    (C' : Set ↥Y) (C : Set ↥T.scheme)
    (hC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) J))
    (hC : C ∈ intersectionComponents T.boundary J)
    (hgen : ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ) :
    orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
  have h1 := orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hC'
  have h2 := orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC
  have hg := hgen (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have h3 := hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hC').genericPoint
  exact h1.trans (h3.trans ((congrArg (orderAt T.ideal) hg).trans h2.symm))

/- English proof (authored)
A zero upper minimum gives the first outcome. Otherwise the lower minimum is positive and at most the upper one. Strict inequality gives the strict invariant comparison by size. If sizes agree, the upper maximum order is at most the lower one, and strict inequality gives the comparison by the reversed order entry. If these orders also agree, transport a component attaining the upper choice to the lower selection with the same positions. It remains of maximum order and the same size. The lower choice is lexicographically at most that selection by its optimality, and the sorted positions of that selection equal the upper choice's positions. This gives strict comparison by the index list or equality of all entries.
-/
theorem minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g) :
    minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 ∨
      (centerInvariant T.ideal T.mult T.boundary).Le
        (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) := by
  by_cases h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary = 0
  · exact Or.inl h0'
  refine Or.inr ?_
  obtain ⟨h0, hle⟩ := minIndexCard_ne_zero_and_le_pullbackOverField hGeom T Y k' q g hT hT' hP h0'
  rw [centerInvariant_le_iff, centerInvariant_lt_iff_lex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl (Or.inl hlt)
  have hmaxle := maxCandidateOrder_le_of_minIndexCard_eq hGeom T Y k' q g hT hT' hP heq.symm h0
  rcases lt_or_eq_of_le hmaxle with hmlt | hmeq
  · exact Or.inl (Or.inr ⟨heq, Or.inl hmlt⟩)
  have hoptT := lexMaxIndices_spec hGeom hT h0
  have hoptT' := lexMaxIndices_spec hGeom hT' h0'
  have hbest' : ∃ C : Set ↥Y,
      IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary
        (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary)
        (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) C ∧
        orderAlong (T.pullbackOverField Y k' q g).ideal C =
          maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary := And.left hoptT'
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hmemC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary) := And.left (And.right hcand')
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
      orderAlong (T.pullbackOverField Y k' q g).ideal C' := And.right (And.right hcand')
  have hex : ∃ B : Finset (Fin T.boundary.length),
      Finset.image (pullbackIndex T Y k' q g) B =
          lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary ∧
        B.card = (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary).card := by
    refine ⟨Finset.image (pullbackIndexSymm T Y k' q g)
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary), ?_, ?_⟩
    · rw [Finset.image_image]
      have hcomp : (pullbackIndex T Y k' q g) ∘ (pullbackIndexSymm T Y k' q g) = id :=
        funext (pullbackIndex_pullbackIndexSymm T Y k' q g)
      rw [hcomp, Finset.image_id]
    · exact Finset.card_image_of_injective _ (pullbackIndexSymm_injective T Y k' q g)
  obtain ⟨B, hBim, hBcard⟩ := hex
  have hmemB : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) B) := by
    rw [hBim]
    exact hmemC'
  obtain ⟨C, hC, -, hgenericPt⟩ := hP.componentsDown B C' hmemB
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP B C' C hmemB hC hgenericPt
  have hcardB : B.card = minIndexCard T.ideal T.mult T.boundary := by
    rw [hBcard, card_lexMaxIndices hGeom hT' h0']
    exact heq.symm
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [← hordEq]
    exact hmultC'
  have hmaxC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [← hordEq, hordC']
    exact hmeq
  have hbestB : IsMaxOrderIndexSet T.ideal T.mult T.boundary B :=
    Exists.intro C (And.intro (And.intro hcardB (And.intro hC hmultC)) hmaxC)
  have hnotlex := And.right hoptT B hbestB
  have hsp : sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) =
      sortedIndices B := by
    rw [← hBim]
    exact sortedIndices_image_pullbackIndex T Y k' q g B
  rcases trichotomous_of (List.Lex (· < ·))
      (sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
      (sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) with
    hlex | hlexeq | hlex
  · exact Or.inl (Or.inr ⟨heq, Or.inr ⟨hmeq.symm, hlex⟩⟩)
  · exact Or.inr ⟨heq, hmeq.symm, hlexeq⟩
  · rw [hsp] at hlex
    exact absurd hlex hnotlex

/- English proof (authored)
An index belongs to either chosen set exactly when its position occurs in the corresponding sorted list. The lists agree by hypothesis. Each position in the upper set is therefore the position of a lower chosen index, and the pullback map carries that lower index to the given upper one. Conversely, pulling back a chosen lower index gives the same position in the upper list and hence an upper chosen index.
-/
theorem lexMaxIndices_pullbackOverField_eq_image (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (h : sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) =
      sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) :
    lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary) := by
  apply Finset.ext
  intro j'
  constructor
  · intro hj'
    have hmem : ((j' : ℕ)) ∈ sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) :=
      (mem_sortedIndices _ _).2 ⟨j', hj', rfl⟩
    rw [← h] at hmem
    obtain ⟨j, hj, hval⟩ := (mem_sortedIndices _ _).1 hmem
    refine Finset.mem_image.2 ⟨j, hj, ?_⟩
    apply Fin.val_injective
    rw [pullbackIndex_val]
    exact hval
  · intro hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    have hmem : ((j : ℕ)) ∈ sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) :=
      (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
    rw [h] at hmem
    obtain ⟨j2, hj2, hval⟩ := (mem_sortedIndices _ _).1 hmem
    have hj2eq : j2 = pullbackIndex T Y k' q g j := by
      apply Fin.val_injective
      rw [pullbackIndex_val]
      exact hval
    rwa [hj2eq] at hj2

/- English proof (authored)
Replace the two index sets and the two component families by their common values. The open parts of the intersection and their inclusions then agree, so their defining kernels coincide.
-/
private theorem componentUnionIdeal_congr {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J J' : Finset (Fin L.length)) (𝒞 𝒞' : Set (Set ↥Y)) (hJ : J = J') (h𝒞 : 𝒞 = 𝒞')
    (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞))
    (hop' : IsOpen (⇑(intersectionIdeal L J').subschemeι ⁻¹' ⋃₀ 𝒞')) :
    componentUnionIdeal L J 𝒞 hop = componentUnionIdeal L J' 𝒞' hop' := by
  subst hJ
  subst h𝒞
  rfl

/- English proof (authored)
If the common minimum size is zero, both centers are unit ideals, and pullback preserves the unit ideal. Otherwise write the centers as ideals of the selected component unions. Under the given index identification, an upper selected component maps into a lower intersection component with the same generic order. Equality of the maxima and minima makes this lower component selected. Conversely, an upper intersection component mapping into a selected lower one has the same generic order as the component supplied by the comparison. That lower component equals the selected one, since their intersection contains the image of an upper point and distinct lower components are disjoint. The upper component therefore also has the required order and is selected. This identifies the two component families used by the pullback property of the union ideal, which gives the center equality.
-/
theorem monomialCenter_pullbackOverField_eq_comap (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (hmax : maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = maxCandidateOrder T.ideal T.mult T.boundary)
    (hch : lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :
    monomialCenter (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      (monomialCenter T.ideal T.mult T.boundary).comap g := by
  by_cases h0 : minIndexCard T.ideal T.mult T.boundary = 0
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 := by rw [hmin]; exact h0
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0']
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0]
    exact (Scheme.IdealSheafData.comap_top g).symm
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0 := by rw [hmin]; exact h0
    obtain ⟨hop', heq⟩ := hP.comapCenter (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT)
    have hSet : centerComponents (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary =
        {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) ∧
          ∃ C ∈ centerComponents T.ideal T.mult T.boundary, Set.MapsTo (⇑g) C' C} := by
      ext C'
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hmem
        obtain ⟨hcand, hordC'⟩ := (mem_centerComponents_iff _ _ _ C').1 hmem
        obtain ⟨hcardJ', hmemC', hmultC'⟩ := hcand
        rw [hch] at hmemC'
        refine ⟨hmemC', ?_⟩
        obtain ⟨C, hC, hmaps, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
          orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C hmemC' hC hgen
        refine ⟨C, (mem_centerComponents_iff _ _ _ C).2
          ⟨⟨card_lexMaxIndices hGeom hT h0, hC, ?_⟩, ?_⟩, hmaps⟩
        · rw [← hord]
          exact hmultC'
        · rw [← hord, hordC']
          exact hmax
      · rintro ⟨hmemC', C, hCopt, hmaps⟩
        obtain ⟨hcandC, hordC⟩ := (mem_centerComponents_iff _ _ _ C).1 hCopt
        obtain ⟨hcardJ, hCmem, hmultC⟩ := hcandC
        obtain ⟨C₀, hC₀, hmaps₀, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hmemC').nonempty
        have hCC₀ : C₀ = C := by
          by_contra hne
          exact Set.disjoint_left.1
            (hGeom.components_disjoint T hT.valid _ C₀ hC₀ C hCmem hne) (hmaps₀ hx) (hmaps hx)
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C₀ :=
          orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C₀ hmemC' hC₀ hgen
        refine (mem_centerComponents_iff _ _ _ C').2
          ⟨⟨card_lexMaxIndices hGeom hT' h0', ?_, ?_⟩, ?_⟩
        · rw [hch]
          exact hmemC'
        · rw [hord, hCC₀]
          exact hmultC
        · rw [hord, hCC₀, hordC]
          exact hmax.symm
    rw [monomialCenter_eq_componentUnionIdeal hGeom hT' h0',
      monomialCenter_eq_componentUnionIdeal hGeom hT h0, heq]
    exact componentUnionIdeal_congr _ _ _ _ _ hch hSet _ _

/- English proof (authored)
Suppose an upper point maps into the lower center. Its image lies in a selected lower component. Lift this component through the upper point using the component comparison and pull back its chosen index set. This keeps the size, generic order and numeric index positions. The resulting positive-size upper candidate rules out a zero upper minimum and bounds the upper minimum by the lower one. Thus a strict invariant comparison cannot arise from a larger upper minimum. If sizes agree, the lifted candidate bounds the upper maximum order below by the lower maximum, ruling out strict comparison by a smaller upper order. If orders agree as well, the lifted selection maximizes the upper order and has the same sorted positions as the lower choice. Optimality of the upper choice then rules out strict comparison by the index list. This contradiction excludes all upper points from the inverse image of the lower center support. The pullback center has empty support and hence is the unit ideal.
-/
theorem comap_monomialCenter_eq_top (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hkey : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary = 0 ∨
        (centerInvariant T.ideal T.mult T.boundary).Lt
          (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary)) :
    (monomialCenter T.ideal T.mult T.boundary).comap g = ⊤ := by
  refine Blowup.comap_eq_top_of_notMem_support g (monomialCenter T.ideal T.mult T.boundary) ?_
  intro y hy
  have hmem : g y ∈ monomialCenterSet T.ideal T.mult T.boundary := by
    rw [← support_monomialCenter hGeom hT h0]
    exact hy
  rw [monomialCenterSet_eq_sUnion_centerComponents, Set.mem_sUnion] at hmem
  obtain ⟨C, hCopt, hgyC⟩ := hmem
  obtain ⟨hcandC, hordC⟩ :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hCopt
  obtain ⟨-, hmemC, hmultC⟩ := hcandC
  obtain ⟨C', hC'mem, -, hgen⟩ :=
    hP.componentsUp (lexMaxIndices T.ideal T.mult T.boundary) C hmemC y hgyC
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
      (lexMaxIndices T.ideal T.mult T.boundary) C' C hC'mem hmemC hgen
  have hinj : Function.Injective (pullbackIndex T Y k' q g) :=
    (pullbackIndex_strictMono T Y k' q g).injective
  have hcard' : (Finset.image (pullbackIndex T Y k' q g)
      (lexMaxIndices T.ideal T.mult T.boundary)).card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hinj]
    exact card_lexMaxIndices hGeom hT h0
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞)
      ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := by
    rw [hordEq]
    exact hmultC
  have hcand' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' :=
    ⟨hcard', hC'mem, hmultC'⟩
  have hone : 1 ≤ minIndexCard T.ideal T.mult T.boundary := Nat.pos_of_ne_zero h0
  have hspec := minIndexCard_spec (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      ⟨minIndexCard T.ideal T.mult T.boundary, hone,
        Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary), C',
        hcand'⟩
  have hle : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≤ minIndexCard T.ideal T.mult T.boundary :=
    hspec.2.2 _ hone _ _ hcand'
  have hgeone := hspec.1
  rcases hkey with hzero | hlt
  · omega
  rw [centerInvariant_lt_iff_lex] at hlt
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by omega
  rcases hlt with hml | ⟨hmeq, hrest⟩
  · omega
  have hcand'' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' := by
    rw [← hmeq]
    exact hcand'
  have hordC' : orderAlong (T.pullbackOverField Y k' q g).ideal C'
      = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [hordEq]
    exact hordC
  rcases hrest with hmax | ⟨hmaxeq, hlex⟩
  · have hb := (maxCandidateOrder_spec hGeom hT' h0').2.1 _ _ hcand''
    rw [hordC'] at hb
    exact absurd hmax (not_lt.mpr hb)
  have hbest : IsMaxOrderIndexSet (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :=
    ⟨C', hcand'', hordC'.trans hmaxeq⟩
  have hnot := (lexMaxIndices_spec hGeom hT' h0').2 _ hbest
  rw [sortedIndices_image_pullbackIndex T Y k' q g (lexMaxIndices T.ideal T.mult T.boundary)] at hnot
  exact hnot hlex

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
