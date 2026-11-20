import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private def markedPullbackSquareId {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (hT : T.IsAdmissible) : MarkedPullbackSquare T g where
  baseScheme := T.scheme
  topScheme := Y
  bottom := 𝟙 T.scheme
  structMap := T.structMap
  ideal := T.ideal
  mult := T.mult
  boundary := T.boundary
  left := g
  top := 𝟙 Y
  bottom_structMap := Category.id_comp T.structMap
  dim_le := le_rfl
  isPullback := (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  valid := hT

/- English proof (authored)
Use the marked pullback square whose lower map is the identity of the original scheme. Its vertical map is g, so the order comparison in the base-change compatibility gives the stated pointwise equality.
-/
theorem orderAt_comap_of_baseChangeCompatible (hinv : ComapIsoInvariance.{u}) (F : PrincipalizationAssignment.{u}) (n : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (hbc : BaseChangeCompatible hinv F n T g k' q)
    (A : T.scheme.IdealSheafData) (y : ↥Y) :
    orderAt (A.comap g) y = orderAt A (g.base y) :=
  MarkedPullbackSquare.orderAt_comap_verticalMap (markedPullbackSquareId g hT) hT hbc.order A y

/- English proof (authored)
A point in the pulled back marked locus would have order at least the marking. Order compatibility gives the same order at its image, placing that image in the original empty locus. Thus the pulled back locus is empty.
-/
theorem orderAtLeastLocus_comap_eq_empty_of_baseChangeCompatible (hinv : ComapIsoInvariance.{u})
    (F : PrincipalizationAssignment.{u}) (n : ℕ) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    {Y : Scheme.{u}} (g : Y ⟶ T.scheme) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (hbc : BaseChangeCompatible hinv F n T g k' q)
    (h : orderAtLeastLocus T.ideal T.mult = ∅) :
    orderAtLeastLocus (T.ideal.comap g) T.mult = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  intro y hy
  have hy' := (mem_orderAtLeastLocus_iff (T.ideal.comap g) T.mult y).1 hy
  rw [orderAt_comap_of_baseChangeCompatible hinv F n T hT g k' q hbc T.ideal y] at hy'
  have hmem := (mem_orderAtLeastLocus_iff T.ideal T.mult _).2 hy'
  rw [h] at hmem
  simp only [Set.mem_empty_iff_false] at hmem

/- English proof (authored)
The stage transform is defined using the stage scheme, its projection followed by the original structure map, the current ideal and boundary, and the unchanged marking. These are exactly the fields shown.
-/
private theorem transformAt_eq_mk (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    T.transformAt s i =
      MarkedIdealWithBoundary.mk T.base (s.schemeAt i) (s.projectionToBase i ≫ T.structMap) (s.ideal i) T.mult
        (s.boundary i) := rfl

/- English proof (authored)
Apply the dimension bound in the monomial geometry hypotheses to the marked sequence at its final stage. The sequence has the same stage schemes and length as its data, so this bounds the dimension of the stated final scheme.
-/
theorem MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim (hmg : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    krullDimSucc (s.obj s.length) ≤ T.krullDimSucc :=
  hmg.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length le_rfl

/- English proof (authored)
The level admissibility property applies to the final transform of the marked sequence. Its scheme, ideal, and boundary are the final data, and its structure map is the final projection composed with the original one. This is precisely the marked object in the conclusion.
-/
theorem MonomialGeometryHypotheses.isAdmissible_tripleAtLength (hmg : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible := by
  have h := hmg.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl
  rw [transformAt_eq_mk T s.toMarkedSequenceOfBlowups s.length,
    toMarkedSequence_projectionToBase s s.length] at h
  exact h

/- English proof (authored)
Substitute the equal ideal and marking. All remaining fields were already fixed, so admissibility is the same proposition for both constructions.
-/
private theorem isAdmissible_mk_congr {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : X.IdealSheafData} {m₁ m₂ : ℕ}
    {E : List X.IdealSheafData} (hI : I₁ = I₂) (hm : m₁ = m₂)
    (h : (MarkedIdealWithBoundary.mk k X p I₁ m₁ E).IsAdmissible) : (MarkedIdealWithBoundary.mk k X p I₂ m₂ E).IsAdmissible := by
  subst hI
  subst hm
  exact h

def SequenceOfBlowupsPullback.toMarkedPullbackSquare {T T' : MarkedIdealWithBoundary.{u}} (g : T'.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hdim : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc)
    (hval : (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible) :
    MarkedPullbackSquare T g where
  baseScheme := s.obj s.length
  topScheme := s'.obj s'.length
  bottom := s.proj s.length
  structMap := s.proj s.length ≫ T.structMap
  ideal := s.ideal s.length
  mult := T.mult
  boundary := s.boundary s.length
  left := c.lastMap
  top := s'.proj s'.length
  bottom_structMap := rfl
  dim_le := hdim
  isPullback := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  valid := hval

/- English proof (authored)
The final lower object is admissible and its dimension is bounded by that of the original object. This makes the comparison of the final stages a marked pullback square. By the final ideal and marking identities the upstairs object is admissible with the corresponding pullback ideal, and the last boundaries are equivalent. The nonmonomial part clause of base-change compatibility therefore gives the equality of the final factors.
-/
theorem lastNonMonomialPart_eq_comap_lastMap_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap)) :
    lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap := by
  have hmg := hG.monomialInputs
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s
  have hvalS'0 := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'
  have hvalS' := isAdmissible_mk_congr hlastIdeal hmult hvalS'0
  have hmain := hbc.nonMonomial (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS)
    (s'.boundary s'.length) hsameBoundary.symm hvalS'
  have h0 : lastNonMonomialPart T' s' = nonMonomialPart (s'.boundary s'.length) (s'.ideal s'.length) :=
    rfl
  have h1 : lastNonMonomialPart T s = nonMonomialPart (s.boundary s.length) (s.ideal s.length) := rfl
  rw [h0, h1, hlastIdeal]
  exact hmain

/- English proof (authored)
The last upper nonmonomial factor is the pullback of the lower one. The final pullback square and order compatibility identify its order at an upper point with the lower order at the image. The lower maximum bounds that value. Therefore every natural number witnessed by an upper point is at most the lower maximum, so its supremum has the same bound.
-/
theorem maxOrderNonMonomial_le_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap)) :
    maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s := by
  have key : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hvalid : (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.toMarkedSequenceOfBlowups.projectionToSpec s.length)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible :=
    hG.monomialInputs.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl
  have hord : ∀ (J : (s.obj s.length).IdealSheafData) (y : ↥(s'.obj s'.length)),
      orderAt (J.comap c.lastMap) y = orderAt J (c.lastMap.base y) :=
    hbc.order (s.obj s.length) (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length)
      (s.toMarkedSequenceOfBlowups.projectionToSpec s.length) (s.ideal s.length) (s.boundary s.length) hvalid
      (MarkedSequenceOfBlowups.projectionToSpec_eq s.toMarkedSequenceOfBlowups s.length).symm
      (s'.obj s'.length) c.lastMap (s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s'.length)
      c.isPullback_lastMap
  have hmain : ∀ y : ↥(s'.obj s'.length),
      orderAt (lastNonMonomialPart T' s') y ≤ (maxOrderNonMonomial T s : ℕ∞) := by
    intro y
    have h1 : orderAt (lastNonMonomialPart T' s') y
        = orderAt (lastNonMonomialPart T s) (c.lastMap.base y) :=
      (congrArg (fun I : (s'.obj s'.length).IdealSheafData => orderAt I y) key).trans
        (hord (lastNonMonomialPart T s) y)
    exact le_of_eq_of_le h1
      (orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s (c.lastMap.base y))
  show sSup {m : ℕ | ∃ x : ↥(s'.obj s'.length), (m : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s') x}
      ≤ maxOrderNonMonomial T s
  refine csSup_le' ?_
  intro m hm
  obtain ⟨y, hy⟩ := hm
  have hcast : (m : ℕ∞) ≤ (maxOrderNonMonomial T s : ℕ∞) := hy.trans (hmain y)
  exact_mod_cast hcast

/- English proof (authored)
Every element of the set defining the maximum on S is a natural number witnessed by a point of S with order at least that number. The given hypothesis bounds each such number by K. Hence their supremum is at most K.
-/
private theorem maxOrderOn_le_of_forall {X : Scheme.{u}} (N : X.IdealSheafData) (S : Set ↥X)
    (K : ℕ) (h : ∀ m : ℕ, ∀ x ∈ S, (m : ℕ∞) ≤ orderAt N x → m ≤ K) :
    maxOrderOn N S ≤ K := by
  unfold maxOrderOn
  refine csSup_le' ?_
  intro m hmem
  obtain ⟨x, hx, hmx⟩ := hmem
  exact h m x hx hmx

/- English proof (authored)
The final ideal and its nonmonomial factor both pull back. Order compatibility in the final square gives equality of the respective orders at an upper point and its lower image. Since the markings agree, a point of the upper marked locus maps into the lower marked locus. Thus each natural number witnessed by the upper nonmonomial order there is bounded by the lower maximum on that locus. Taking the supremum gives the assertion.
-/
theorem maxOrderNonMonomialOnOrderLocus_le_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap)) :
    maxOrderNonMonomialOnOrderLocus T' s' ≤ maxOrderNonMonomialOnOrderLocus T s := by
  have hmg := hG.monomialInputs
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s
  have hordLast : ∀ (Aid : (s.obj s.length).IdealSheafData) (y : ↥(s'.obj s'.length)),
      orderAt (Aid.comap c.lastMap) y = orderAt Aid (c.lastMap.base y) :=
    fun Aid y =>
      MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) hT
        hbc.order Aid y
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hmain : maxOrderNonMonomialOnOrderLocus T' s' =
      maxOrderOn (lastNonMonomialPart T' s') (orderAtLeastLocus (s'.ideal s'.length) T'.mult) := rfl
  rw [hmain]
  refine maxOrderOn_le_of_forall _ _ _ ?_
  intro m x' hx' hm
  have hEq1 : orderAt (s'.ideal s'.length) x' = orderAt (s.ideal s.length) (c.lastMap.base x') :=
    (congrArg (fun I => orderAt I x') hlastIdeal).trans (hordLast (s.ideal s.length) x')
  have hEq2 : orderAt (lastNonMonomialPart T' s') x'
      = orderAt (lastNonMonomialPart T s) (c.lastMap.base x') :=
    (congrArg (fun I => orderAt I x') hnonMon).trans (hordLast (lastNonMonomialPart T s) x')
  have h1 : ((T'.mult : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length) x' :=
    (mem_orderAtLeastLocus_iff _ _ _).1 hx'
  have hmult' : ((T.mult : ℕ) : ℕ∞) = ((T'.mult : ℕ) : ℕ∞) := by rw [hmult]
  have h3 : ((T.mult : ℕ) : ℕ∞) ≤ orderAt (s.ideal s.length) (c.lastMap.base x') :=
    hmult'.trans_le (h1.trans_eq hEq1)
  have hxmem : c.lastMap.base x' ∈ orderAtLeastLocus (s.ideal s.length) T.mult :=
    (mem_orderAtLeastLocus_iff _ _ _).2 h3
  have hle := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s (c.lastMap.base x') hxmem
  have hfin : ((m : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := (hm.trans_eq hEq2).trans hle
  exact_mod_cast hfin

/- English proof (authored)
Zero belongs to the defining set because the scheme has the point x₀. The assumed order bound makes the supremum a finite upper bound for every natural number in the set. A nonempty bounded set of natural numbers contains its supremum. The point witnessing that membership is in the order locus at the supremum.
-/
private theorem orderAtLeastLocus_sSup_nonempty {X : Scheme.{u}} (N : X.IdealSheafData)
    (x₀ : ↥X)
    (hbound : ∀ x : ↥X,
      orderAt N x ≤ ((sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y} : ℕ) : ℕ∞)) :
    (orderAtLeastLocus N (sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y})).Nonempty := by
  have hne : {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}.Nonempty := by
    refine ⟨0, x₀, ?_⟩
    simp
  have hbdd : BddAbove {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y} := by
    refine ⟨sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}, ?_⟩
    intro m hm
    obtain ⟨y, hy⟩ := hm
    have h := hy.trans (hbound y)
    exact_mod_cast h
  obtain ⟨y, hy⟩ := Nat.sSup_mem hne hbdd
  exact ⟨y, (mem_orderAtLeastLocus_iff N _ y).2 hy⟩

/- English proof (authored)
The upper maximum is bounded by the lower maximum, so the common marking is at most the lower maximum. The upper continuation condition supplies a point, whose image shows the lower final scheme is nonempty. The lower nonmonomial order is bounded by its finite maximum. Hence that maximum is attained and its locus is nonempty, giving the second continuation condition downstairs.
-/
theorem nonMonomialOrderReductionContinues_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hcont : NonMonomialOrderReductionContinues T' s') : NonMonomialOrderReductionContinues T s := by
  have hle : maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s :=
    maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s'
      c hlastIdeal hsameBoundary
  unfold NonMonomialOrderReductionContinues at hcont ⊢
  obtain ⟨h1, h2⟩ := hcont
  obtain ⟨x', -⟩ := h2
  rw [hmult] at h1
  refine ⟨le_trans h1 hle, ?_⟩
  have hbound : ∀ x : ↥(s.obj s.length),
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞) :=
    fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  exact orderAtLeastLocus_sSup_nonempty (lastNonMonomialPart T s) (c.lastMap.base x') hbound

/- English proof (authored)
The upper continuation condition gives a maximum on the upper marked locus of at least one. The pullback bound makes this maximum at most the lower one, so the lower maximum is also at least one.
-/
theorem companionIdealReductionContinues_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hcont : CompanionIdealReductionContinues T' s') : CompanionIdealReductionContinues T s := by
  have hle : maxOrderNonMonomialOnOrderLocus T' s' ≤ maxOrderNonMonomialOnOrderLocus T s :=
    maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
      s s' c hlastIdeal hsameBoundary
  unfold CompanionIdealReductionContinues at hcont ⊢
  omega

/- English proof (authored)
Ideal pullback preserves sums and powers. Apply these properties to the sum of the two powers.
-/
private theorem comap_pow_sup_pow {A B : Scheme.{u}} (f : A ⟶ B) (N J : B.IdealSheafData)
    (a b : ℕ) : (N ^ a ⊔ J ^ b).comap f = (N.comap f) ^ a ⊔ (J.comap f) ^ b := by
  simp only [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow]

/- English proof (authored)
Replace the two upper ideals by the pullbacks and identify their exponents with the lower ones. Pullback commutes with the sum and both powers, giving the equality.
-/
private theorem pow_sup_pow_eq_comap_pow_sup_pow {A B : Scheme.{u}} (f : A ⟶ B)
    (N₁ N₂ : B.IdealSheafData) (M₁ M₂ : A.IdealSheafData) (a a' b b' : ℕ)
    (h₁ : M₁ = N₁.comap f) (h₂ : M₂ = N₂.comap f) (ha : a = a') (hb : b = b') :
    M₁ ^ a ⊔ M₂ ^ b = (N₁ ^ a' ⊔ N₂ ^ b').comap f := by
  subst h₁
  subst h₂
  subst ha
  subst hb
  exact (comap_pow_sup_pow f N₁ N₂ _ _).symm

/- English proof (authored)
The last ideal and its nonmonomial factor both pull back along the final comparison. The exponents in the companion ideal agree because the markings and the maxima on the marked loci agree. Pullback preserves the two powers and their sum, giving the desired companion ideal.
-/
theorem companionIdeal_eq_comap_lastMap_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hinveq : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderNonMonomialOnOrderLocus T s) :
    companionIdeal T' s' = (companionIdeal T s).comap c.lastMap := by
  have hnonMon := lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim'
    hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary
  unfold companionIdeal
  exact pow_sup_pow_eq_comap_pow_sup_pow _ _ _ _ _ T'.mult T.mult (maxOrderNonMonomialOnOrderLocus T' s') (maxOrderNonMonomialOnOrderLocus T s)
    hnonMon hlastIdeal hmult hinveq

/- English proof (authored)
The dimension bound permits evaluation of the recursive sequence. The markedness test returns no data, so the conditional append returns the input sequence.
-/
private theorem appendRecursivePrincipalization_eq_self_of_eq_none (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)
    (h : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) = none) :
    appendRecursivePrincipalization hinv T rc s J μ = s := by
  have h1 : appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) hd) := by
    unfold appendRecursivePrincipalization
    exact dif_pos hd
  rw [h1]
  unfold appendIfMarked
  rw [h]

/- English proof (authored)
The dimension bound allows the recursive call and the markedness test returns d. Reading the successful branch of the conditional append gives the original sequence followed by d.
-/
private theorem appendRecursivePrincipalization_eq_append_of_eq_some (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)
    (d : MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
      (s.boundary s.length))
    (h : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) = some d) :
    appendRecursivePrincipalization hinv T rc s J μ = s.append d hinv := by
  have h1 : appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) hd) := by
    unfold appendRecursivePrincipalization
    exact dif_pos hd
  rw [h1]
  unfold appendIfMarked
  rw [h]

private def markedPullbackSquareAtLength (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hdim : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc)
    (hJ : (tripleAtLength T s J μ).IsAdmissible) :
    MarkedPullbackSquare T g where
  baseScheme := s.obj s.length
  topScheme := s'.obj s'.length
  bottom := s.proj s.length
  structMap := s.proj s.length ≫ T.structMap
  ideal := J
  mult := μ
  boundary := s.boundary s.length
  left := c.lastMap
  top := s'.proj s'.length
  bottom_structMap := rfl
  dim_le := hdim
  isPullback := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  valid := hJ

/- English proof (authored)
Each given output is present, so each markedness test has succeeded. Uniqueness of a present value identifies d and d′ with the reassigned marked data for the two sequences. Reassigning those markings keeps the underlying blowup data, and the conversion of a sequence comparison to its underlying data supplies the required comparison.
-/
private theorem nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k₁)} {q : Y ⟶ Spec (CommRingCat.of k₂)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    {I' : Y.IdealSheafData} {m' : ℕ} {E' : List Y.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m' E')
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (K : (s'.obj s'.length).IdealSheafData) (ν : ℕ)
    (f : s'.obj s'.length ⟶ s.obj s.length)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length))
    (σ' : MarkedSequenceOfBlowups (s'.proj s'.length ≫ q) K ν (s'.boundary s'.length))
    (d : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (d' : MarkedBlowupSequenceData (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' (s'.boundary s'.length))
    (hrem : markedDataOfSeq s J μ σ = some d) (hrem' : markedDataOfSeq s' K ν σ' = some d')
    (cc : SequenceOfBlowupsPullback f σ'.toSequenceOfBlowups σ.toSequenceOfBlowups) :
    Nonempty (SequenceOfBlowupsPullback f d'.toSequenceOfBlowups d.toSequenceOfBlowups) := by
  classical
  by_cases hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p)
      (s.ideal s.length) m (s.boundary s.length)
  · by_cases hm' : (MarkedBlowupSequenceData.ofMarkedSequence σ').IsMarked (s'.proj s'.length ≫ q)
        (s'.ideal s'.length) m' (s'.boundary s'.length)
    · have he : markedDataOfSeq s J μ σ = some ((MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData
          (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) hm) := by
        unfold markedDataOfSeq
        exact dif_pos hm
      have he' : markedDataOfSeq s' K ν σ' = some ((MarkedBlowupSequenceData.ofMarkedSequence σ').toMarkedBlowupSequenceData
          (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' (s'.boundary s'.length) hm') := by
        unfold markedDataOfSeq
        exact dif_pos hm'
      have hdd := Option.some.inj (hrem.symm.trans he)
      have hdd' := Option.some.inj (hrem'.symm.trans he')
      subst hdd
      subst hdd'
      exact ⟨SequenceOfBlowupsPullback.toBlowupDataOfSeq cc⟩
    · have hnone : markedDataOfSeq s' K ν σ' = none := by
        unfold markedDataOfSeq
        exact dif_neg hm'
      exact absurd (hrem'.symm.trans hnone) (Option.some_ne_none d')
  · have hnone : markedDataOfSeq s J μ σ = none := by
      unfold markedDataOfSeq
      exact dif_neg hm
    exact absurd (hrem.symm.trans hnone) (Option.some_ne_none d)

/- English proof (authored)
The geometric dimension bounds permit both recursive calls. The hypothesis on the markedness tests gives either two failed tests or two successful tests. In the failed case both appends leave the existing comparison unchanged. In the successful case the final marked pullback square, admissibility, order and dimension conditions, and boundary equivalence let the assignment's base-change rule compare the two recursive sequences. Their underlying blowup comparison persists after giving them the original markings. Append that comparison to the existing comparison to obtain the required one.
-/
theorem nonempty_sequenceOfBlowupsPullback_appendRecursive (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (_hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (_hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (_htopIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hJ' : (tripleAtLength T' s' (J.comap c.lastMap) μ).IsAdmissible)
    (hord : ∀ x : ↥(s.obj s.length), orderAt J x ≤ (μ : ℕ∞))
    (hmark : ∀ (h : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' (J.comap c.lastMap) μ).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) h) = none ↔
        markedDataOfSeq s' (J.comap c.lastMap) μ
          (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) h') = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have hmg := hG.monomialInputs
  have hdimS : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc :=
    MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hdimS'T : krullDimSucc (s'.obj s'.length) ≤ T'.krullDimSucc :=
    MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T' hT' s'
  have hdimS'n : krullDimSucc (s'.obj s'.length) ≤ n := le_trans hdimS'T hdim'
  have hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc := hdimS
  have hd' : (tripleAtLength T' s' (J.comap c.lastMap) μ).krullDimSucc ≤ T'.krullDimSucc := hdimS'T
  have hiff := hmark hd hd'
  cases hq : markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) with
  | none =>
      have hq2 : markedDataOfSeq s' (J.comap c.lastMap) μ
          (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') = none := hiff.mp hq
      rw [appendRecursivePrincipalization_eq_self_of_eq_none hinv T (principalizationOfDimLe T A) s J μ hd hq,
        appendRecursivePrincipalization_eq_self_of_eq_none hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ hd' hq2]
      exact ⟨c⟩
  | some d =>
      cases hq' : markedDataOfSeq s' (J.comap c.lastMap) μ
          (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') with
      | none => exact absurd (hq.symm.trans (hiff.mpr hq')) (Option.some_ne_none d)
      | some d' =>
          have hrule : IsPullbackBlowupSequence c.lastMap
              (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd').toSequenceOfBlowups
              (principalizationOfDimLe T A (tripleAtLength T s J μ) hd).toSequenceOfBlowups :=
            hbc.rule (markedPullbackSquareAtLength T T' g s s' c J μ hdimS hJ) hord (s'.boundary s'.length)
              hsameBoundary.symm hJ' hdimS'n
          obtain ⟨cc⟩ := hrule.nonempty_sequenceOfBlowupsPullback
          obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq s s' J μ (J.comap c.lastMap) μ
            c.lastMap (principalizationOfDimLe T A (tripleAtLength T s J μ) hd)
            (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') d d' hq hq' cc
          rw [appendRecursivePrincipalization_eq_append_of_eq_some hinv T (principalizationOfDimLe T A) s J μ hd d hq,
            appendRecursivePrincipalization_eq_append_of_eq_some hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ
              hd' d' hq']
          exact (isPullbackBlowupSequence_append_of_two_fields g s d s' d' hinv c e).nonempty_sequenceOfBlowupsPullback

/- English proof (authored)
The underlying point map of a composite is the composite of the underlying point maps. Evaluate the three arrows in their order of application at a.
-/
private theorem base_comp_comp_apply {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (a : ↥A) : (f ≫ g ≫ h).base a = h.base (g.base (f.base a)) := rfl

private noncomputable def markedBlowupSequenceDataAtEndOfIsMarked {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length)) :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) :=
  (MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
    (s.boundary s.length) hm

/- English proof (authored)
Admissibility of the starting triple gives admissibility at every stage. The order-locus inclusion along the transition to stage zero sends z into the stage-zero locus at μ. The initial ideal is pulled back from J along the initial isomorphism, so its order locus is the inverse image of the locus of J. The projection to the starting scheme passes through that isomorphism, and its image of z therefore lies in the locus of J.
-/
private theorem projectionToBase_mem_orderAtLeastLocus_tripleAtLength (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length))
    (j : ℕ) (hj : j ≤ σ.toSequenceOfBlowups.length) (z : ↥(σ.toSequenceOfBlowups.schemeAt j))
    (hz : z ∈ orderAtLeastLocus (σ.ideal j) μ) :
    (σ.toSequenceOfBlowups.projectionToBase j).base z ∈ orderAtLeastLocus J μ := by
  have hval : ∀ l ≤ σ.toSequenceOfBlowups.length, ((tripleAtLength T s J μ).transformAt σ l).IsAdmissible := by
    intro l hl
    exact hG.monomialInputs.level_valid (tripleAtLength T s J μ) hJ σ l hl
  have hsub := MarkedSequenceOfBlowups.orderAtLeastLocus_subset_preimage_transitionMap
    (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs)
    (tripleAtLength T s J μ) σ hval μ le_rfl 0 j (Nat.zero_le j) hj
  have h0 : (σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z ∈ orderAtLeastLocus (σ.ideal 0) μ := hsub hz
  rw [σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero J μ] at h0
  have hcomp : (σ.toSequenceOfBlowups.projectionToBase j).base z
      = (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z) := by
    rw [SequenceOfBlowups.projectionToBase_def]
    simp
  rw [hcomp]
  exact h0

/- English proof (authored)
At the joining index, the center is the first center of the appended sequence transported by its initial isomorphism and the join identification. A point of this center corresponds to a point at the first tail stage of order at least μ for the tail ideal. Projecting this point to the joining scheme puts it in the locus of J, and the projection formula for the append identifies its original ambient image with that of z.

After the join, shift the index by the prefix length. The center point corresponds to a point of the tail center at that index, hence belongs to the tail stage's marked order locus. Its projection to the joining scheme belongs to the locus of J by the order-locus comparison. The projection of the append factors through this tail projection and the prefix's last projection, giving the claimed equality of images.
-/
private theorem exists_mem_orderAtLeastLocus_of_mem_center_append (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length))
    (i : ℕ) (hi₀ : s.length ≤ i)
    (hi : i < (s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).length)
    (z : ↥((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).obj i))
    (hz : z ∈ ((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).center i).support) :
    ∃ x : ↥(s.obj s.length), x ∈ orderAtLeastLocus J μ ∧
      ((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).proj i).base z = (s.proj s.length).base x := by
  have hdl : (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm).length = σ.toSequenceOfBlowups.length := rfl
  rw [MarkedBlowupSequenceData.append_length, hdl] at hi
  have hprojd : ∀ j : ℕ, (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm).proj j = σ.toSequenceOfBlowups.projectionToBase j := by
    intro j
    refine Eq.trans (MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) j) ?_
    exact BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups σ.toSequenceOfBlowups j
  rcases Nat.eq_or_lt_of_le hi₀ with heq | hlt
  · subst heq
    have hσ0 : 0 < σ.toSequenceOfBlowups.length := by omega
    have hz1 : z ∈ ((s.appendToBlowupSequenceData (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)).center s.length).support := hz
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)] at hz1
    have hz2 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1
    have hz3 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz2
    have hz4 : (σ.toSequenceOfBlowups.isoZero.inv).base
        ((eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)
          (le_refl s.length))).base z) ∈ orderAtLeastLocus (σ.ideal 0) μ :=
      σ.center_order 0 hσ0 hz3
    have hx0 := projectionToBase_mem_orderAtLeastLocus_tripleAtLength hG hinv T s J μ hJ σ 0 (Nat.zero_le _) _ hz4
    refine ⟨(eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)
      (le_refl s.length))).base z, ?_, ?_⟩
    · rw [SequenceOfBlowups.projectionToBase_zero] at hx0
      have hcan : ∀ u : ↥(s.obj s.length),
          (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.isoZero.inv).base u) = u := by
        intro u
        simp
      rwa [hcan] at hx0
    · rw [MarkedBlowupSequenceData.append_projectionToBase,
        MarkedBlowupSequenceData.appendProjectionToBase_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) (le_refl s.length)]
      exact AlgebraicGeometry.Scheme.Hom.comp_apply _ _ z
  · have hkσ : i - s.length < σ.toSequenceOfBlowups.length := by omega
    have hz1 : z ∈ ((s.appendToBlowupSequenceData (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)).center i).support := hz
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt] at hz1
    have hz2 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1
    have hz3 : ((eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)
        hlt)).base z) ∈ orderAtLeastLocus (σ.ideal (i - s.length)) μ :=
      σ.center_order (i - s.length) hkσ hz2
    have hx0 := projectionToBase_mem_orderAtLeastLocus_tripleAtLength hG hinv T s J μ hJ σ (i - s.length)
      (le_of_lt hkσ) _ hz3
    refine ⟨_, hx0, ?_⟩
    rw [MarkedBlowupSequenceData.append_projectionToBase,
      MarkedBlowupSequenceData.appendProjectionToBase_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt, hprojd]
    exact base_comp_comp_apply _ _ _ z

/- English proof (authored)
The appended center point projects via a point x of the locus of J on the final lower scheme. If its further image were the image of an upper base point, the final pullback square would lift this pair to a point of the final upper scheme. Order invariance in that square gives order at least μ for the pullback of J at the lifted point. This contradicts emptiness of that locus, so the two images differ.
-/
private theorem append_proj_center_ne_base_of_orderAtLeastLocus_empty (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u})
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible)
    (n : ℕ) (A : PrincipalizationAssignment.{u})
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) μ = ∅)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length))
    (D : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hD : D = s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv)
    (i : ℕ) (hi₀ : s.length ≤ i) (hi : i < D.length)
    (z : ↥(D.obj i)) (hz : z ∈ (D.center i).support) (y : ↥T'.scheme) :
    g.base y ≠ ((D.proj i).base z) := by
  subst hD
  obtain ⟨x, hx, hproj⟩ :=
    exists_mem_orderAtLeastLocus_of_mem_center_append hG hinv T s J μ hJ σ hm i hi₀ hi z hz
  intro hcon
  rw [hproj] at hcon
  have hsq : IsPullback c.lastMap (s'.proj s'.length) (s.proj s.length) g := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hsq x y hcon.symm
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hG.monomialInputs T hT s
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hG.monomialInputs T hT s
  have hord : orderAt (J.comap c.lastMap) w = orderAt J (c.lastMap.base w) :=
    MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) hT
      hbc.order J w
  have hmem : w ∈ orderAtLeastLocus (J.comap c.lastMap) μ := by
    rw [mem_orderAtLeastLocus_iff, hord, hw]
    exact (mem_orderAtLeastLocus_iff J μ x).1 hx
  rw [hempty] at hmem
  simp only [Set.mem_empty_iff_false] at hmem

/- English proof (authored)
If the dimension test fails or the recursive sequence fails its markedness test, the result is the original sequence. There could then be no index at or beyond the original length strictly smaller than the resulting length. Thus the stated index belongs to a successful append. Apply the image-disjointness result for centers of such an append to the empty pulled back locus.
-/
theorem appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (_hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (_hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hdim' : T'.krullDimSucc ≤ n)
    (_hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (_htopIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (_hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) μ = ∅)
    (i : ℕ) (hi₀ : s.length ≤ i) (hi : i < (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).length)
    (z : ↥((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).obj i))
    (hz : z ∈ ((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).center i).support) (y : ↥T'.scheme) :
    g.base y ≠ ((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).proj i).base z := by
  classical
  by_cases hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc
  · by_cases hm : (MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T (principalizationOfDimLe T A) s J μ hd)).IsMarked
        (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)
    · exact append_proj_center_ne_base_of_orderAtLeastLocus_empty hG hinv T T' g hT n A hbc s s' c J μ hJ hempty
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s J μ hd) hm (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ)
        (appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s J μ hd hm) i hi₀ hi z hz y
    · exfalso
      have hrs : markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) = none := by
        unfold markedDataOfSeq
        exact dif_neg hm
      have he : appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ = s :=
        appendRecursivePrincipalization_eq_self_of_eq_none hinv T (principalizationOfDimLe T A) s J μ hd hrs
      rw [he] at hi
      omega
  · exfalso
    have he : appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ = s := by
      unfold appendRecursivePrincipalization
      exact dif_neg hd
    rw [he] at hi
    omega

/- English proof (authored)
Evaluate the dimension test. If it fails, the result is the starting sequence. If it succeeds, evaluate the markedness test of the assigned sequence. A failed test again returns the starting sequence, while a successful test supplies a marked tail and returns its append.
-/
private theorem appendRecursivePrincipalization_eq_self_or_append (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    appendRecursivePrincipalization hinv T rc s J μ = s ∨
      ∃ t : MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
        (s.boundary s.length), appendRecursivePrincipalization hinv T rc s J μ = s.append t hinv := by
  unfold appendRecursivePrincipalization
  by_cases hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc
  · rw [dif_pos hd]
    unfold appendIfMarked
    cases hrem : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) with
    | none => exact Or.inl rfl
    | some d => exact Or.inr ⟨d, rfl⟩
  · rw [dif_neg hd]
    exact Or.inl rfl

/- English proof (authored)
If the recursive operation leaves the lower sequence unchanged, retain the given pullback comparison. If it appends a tail, the empty pulled back order locus guarantees that the projections of all appended center points miss the image of the upper base. The marked append has the underlying append of blowup data with the same centers and projections. The comparison theorem for an appended tail with centers missing the upper image therefore extends the lower side while retaining the existing upper sequence.
-/
theorem nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) μ = ∅) :
    Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  rcases appendRecursivePrincipalization_eq_self_or_append hinv T (principalizationOfDimLe T A) s J μ with heq | ⟨t, heq⟩
  · rw [heq]
    exact ⟨c⟩
  · have hmiss := appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim
      hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary J μ hJ hempty
    have hconcat : (s.append t hinv).toBlowupSequenceData
        = s.toBlowupSequenceData.append t.toBlowupSequenceData := by
      rw [MarkedBlowupSequenceData.append_toBlowupSequenceData]
      rfl
    have hseq : (s.append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        = (s.toBlowupSequenceData.append t.toBlowupSequenceData).toSequenceOfBlowups :=
      congrArg (fun D : BlowupSequenceData T.scheme => D.toSequenceOfBlowups) hconcat
    have h0 : ∀ i : ℕ, s.length ≤ i → i < (s.append t hinv).length →
        ∀ z : ↥((s.append t hinv).obj i), z ∈ ((s.append t hinv).center i).support →
          ∀ y : ↥T'.scheme, g.base y ≠ ((s.append t hinv).proj i).base z := by
      rw [← heq]
      exact hmiss
    have h0' : ∀ i : ℕ, s.length ≤ i → i < s.length + t.length →
        ∀ z : ↥((s.append t hinv).obj i), z ∈ ((s.append t hinv).center i).support →
          ∀ y : ↥T'.scheme, g.base y ≠ ((s.append t hinv).proj i).base z := by
      intro i hi0 hi
      refine h0 i hi0 ?_
      rw [MarkedBlowupSequenceData.append_length]
      exact hi
    have hproj : ∀ i : ℕ,
        (s.append t hinv).toBlowupSequenceData.projectionToBase i = (s.append t hinv).proj i := by
      intro i
      rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups]
      exact (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s.append t hinv).toBlowupSequenceData i).symm
    have key : ∀ i : ℕ, s.toBlowupSequenceData.length ≤ i →
        i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length →
        ∀ z : ↥((s.toBlowupSequenceData.append t.toBlowupSequenceData).obj i),
          z ∈ ((s.toBlowupSequenceData.append t.toBlowupSequenceData).center i).support →
          ∀ y : ↥T'.scheme,
            g.base y ≠ ((s.toBlowupSequenceData.append t.toBlowupSequenceData).projectionToBase i).base z := by
      rw [← hconcat]
      intro i hi0 hi z hz y
      rw [hproj i]
      exact h0' i hi0 hi z hz y
    rw [heq, hseq]
    exact SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers g s'.toBlowupSequenceData s.toBlowupSequenceData
      t.toBlowupSequenceData c key

/- English proof (authored)
The nonmonomial continuation conditions give admissibility of both final nonmonomial objects. The upper final nonmonomial ideal is the pullback of the lower one, and the equal maxima give the same marking. The lower maximum bounds all lower orders. With these identifications, the simultaneous markedness-test assumption is the one in the recursive append comparison. Apply it and identify those appends with the two nonmonomial extensions.
-/
theorem nonempty_sequenceOfBlowupsPullback_extendByNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hcont : NonMonomialOrderReductionContinues T s) (hcont' : NonMonomialOrderReductionContinues T' s')
    (hinveq : maxOrderNonMonomial T' s' = maxOrderNonMonomial T s)
    (hmark : ∀ (h : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' ((lastNonMonomialPart T s).comap c.lastMap)
        (maxOrderNonMonomial T s)).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (principalizationOfDimLe T A (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) h) = none ↔
        markedDataOfSeq s' ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s)
          (principalizationOfDimLe T' A
            (tripleAtLength T' s' ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s)) h')
          = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hJ : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).IsAdmissible :=
    isAdmissible_nonMonomialTriple hG hT s hcont
  have hJ' : (tripleAtLength T' s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s')).IsAdmissible :=
    isAdmissible_nonMonomialTriple hG hT' s' hcont'
  rw [hnonMon, hinveq] at hJ'
  have hord : ∀ x : ↥(s.obj s.length),
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞) :=
    fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have key := nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim'
    hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
    hJ hJ' hord hmark
  have hL : extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s
      = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s) := rfl
  have hU : extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s'
      = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s') := rfl
  rw [hnonMon, hinveq] at hU
  rw [hL, hU]
  exact key

/- English proof (authored)
Substitute the equal ideal and marking. The two recursive append constructions now have identical inputs and are equal.
-/
private theorem appendRecursivePrincipalization_congr (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν) :
    appendRecursivePrincipalization hinv T rc s J μ = appendRecursivePrincipalization hinv T rc s K ν := by
  subst hJK
  subst hμν
  rfl

/- English proof (authored)
The final marked objects differ through the given ideal and marking, which are equal by assumption. Substituting the equalities transfers admissibility.
-/
private theorem isAdmissible_tripleAtLength_congr (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν)
    (h : (tripleAtLength T s J μ).IsAdmissible) : (tripleAtLength T s K ν).IsAdmissible := by
  subst hJK
  subst hμν
  exact h

/- English proof (authored)
The equality of the maxima and of the original markings gives equal companion markings. The companion ideal comparison identifies the upper companion ideal with the pullback of the lower one. Both companion triples are admissible by continuation, and the lower companion ideal has order bounded by its marking. The recursive append comparison now applies using the simultaneous markedness tests. These appends are the stated companion extensions after substituting the ideal and marking identities.
-/
theorem nonempty_sequenceOfBlowupsPullback_extendByCompanionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hcont : CompanionIdealReductionContinues T s) (hcont' : CompanionIdealReductionContinues T' s')
    (hinveq : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderNonMonomialOnOrderLocus T s)
    (hmark : ∀ (h : (tripleAtLength T s (companionIdeal T s)
        (T.mult * maxOrderNonMonomialOnOrderLocus T s)).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
        (T.mult * maxOrderNonMonomialOnOrderLocus T s)).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
          (principalizationOfDimLe T A
            (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) h) = none ↔
        markedDataOfSeq s' ((companionIdeal T s).comap c.lastMap) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
          (principalizationOfDimLe T' A
            (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
              (T.mult * maxOrderNonMonomialOnOrderLocus T s)) h') = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hJideal : companionIdeal T' s' = (companionIdeal T s).comap c.lastMap :=
    companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary hinveq
  have hmu : T'.mult * maxOrderNonMonomialOnOrderLocus T' s' = T.mult * maxOrderNonMonomialOnOrderLocus T s := by
    rw [hinveq, hmult]
  have hJ : (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)).IsAdmissible :=
    companionTriple_isAdmissible hG hT s hcont
  have hJ'0 : (tripleAtLength T' s' (companionIdeal T' s') (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')).IsAdmissible :=
    companionTriple_isAdmissible hG hT' s' hcont'
  have hJ' : (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
      (T.mult * maxOrderNonMonomialOnOrderLocus T s)).IsAdmissible :=
    isAdmissible_tripleAtLength_congr T' s' (companionIdeal T' s')
      ((companionIdeal T s).comap c.lastMap) (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')
      (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu hJ'0
  have hord := orderAt_companionIdeal_le hG hT s hcont
  have hA : extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s
      = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) := rfl
  have hB0 : extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s'
      = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (companionIdeal T' s')
        (T'.mult * maxOrderNonMonomialOnOrderLocus T' s') := rfl
  have hB : extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s'
      = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' ((companionIdeal T s).comap c.lastMap)
        (T.mult * maxOrderNonMonomialOnOrderLocus T s) :=
    hB0.trans
      (appendRecursivePrincipalization_congr hinv T' (principalizationOfDimLe T' A) s' (companionIdeal T' s')
        ((companionIdeal T s).comap c.lastMap) (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')
        (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu)
  rw [hA, hB]
  exact nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
    hideal hbdry hbc s s' c hlastIdeal hsameBoundary (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
    hJ hJ' hord hmark

/- English proof (authored)
Identify the pulled back lower factor with the upper nonmonomial factor. Its order at every point is at most the upper maximum, which is strictly less than the lower maximum. Hence no point reaches the lower threshold.
-/
theorem orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : PrincipalizationAssignment.{u})
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hlt : maxOrderNonMonomial T' s' < maxOrderNonMonomial T s) :
    orderAtLeastLocus ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) = ∅ := by
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  refine Set.eq_empty_of_subset_empty ?_
  intro y hy
  have hy' := (mem_orderAtLeastLocus_iff ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) y).1 hy
  rw [← hnonMon] at hy'
  have hle : orderAt (lastNonMonomialPart T' s') y ≤ ((maxOrderNonMonomial T' s' : ℕ) : ℕ∞) :=
    orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT' s' y
  have hcast : ((maxOrderNonMonomial T s : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomial T' s' : ℕ) : ℕ∞) := hy'.trans hle
  have hnat : maxOrderNonMonomial T s ≤ maxOrderNonMonomial T' s' := by exact_mod_cast hcast
  exact absurd hnat (not_le.mpr hlt)

/- English proof (authored)
If a is infinite, the bound by a holds automatically. Otherwise write a as a natural number. Commute the factors on the left so both sides have the positive factor p. Cancelling this factor in the natural-number inequality gives m at most a.
-/
private theorem natCast_le_of_natCast_mul_le_mul (m p : ℕ) (hp : 1 ≤ p) (a : ℕ∞)
    (h : ((m * p : ℕ) : ℕ∞) ≤ ((p : ℕ) : ℕ∞) * a) : ((m : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact le_top
  · obtain ⟨a₀, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    have h' : m * p ≤ p * a₀ := by exact_mod_cast h
    have h'' : p * m ≤ p * a₀ := by
      rw [Nat.mul_comm p m]
      exact h'
    have hle : m ≤ a₀ := Nat.le_of_mul_le_mul_left h'' (by omega)
    exact_mod_cast hle

/- English proof (authored)
The pulled back lower companion ideal is the sum of the powers of the upper nonmonomial factor and upper final ideal, with the lower exponents. The lower maximum is positive by the strict inequality, and the marking is positive. If a point attained the lower companion threshold, the minimum formula would make both weighted orders at least that threshold. Cancelling the respective positive exponents shows that the point lies in the upper marked order locus and its nonmonomial order there is at least the lower maximum. This exceeds the upper maximum on that locus, a contradiction.
-/
theorem orderAtLeastLocus_comap_companionIdeal_eq_empty_of_lt (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : PrincipalizationAssignment.{u})
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hlt : maxOrderNonMonomialOnOrderLocus T' s' < maxOrderNonMonomialOnOrderLocus T s) :
    orderAtLeastLocus ((companionIdeal T s).comap c.lastMap) (T.mult * maxOrderNonMonomialOnOrderLocus T s) = ∅ := by
  have hmg := hG.monomialInputs
  have hvalS' := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'
  have hchar : CharZero T'.base := hvalS'.charZero
  have hsmooth : AlgebraicGeometry.Smooth (s'.proj s'.length ≫ T'.structMap) := hvalS'.smooth
  have hm1 : 1 ≤ T.mult := hT.one_le_mult
  have hp1 : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := by omega
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hcompanion : (companionIdeal T s).comap c.lastMap
      = lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s := by
    unfold companionIdeal
    rw [hnonMon, hlastIdeal]
    exact comap_pow_sup_pow c.lastMap (lastNonMonomialPart T s) (s.ideal s.length) T.mult
      (maxOrderNonMonomialOnOrderLocus T s)
  rw [hcompanion]
  refine Set.eq_empty_of_subset_empty ?_
  intro x hx
  exfalso
  have hx0 : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ orderAt (lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x :=
    (mem_orderAtLeastLocus_iff _ _ _).1 hx
  have hsup : orderAt (lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x
      = min (orderAt (lastNonMonomialPart T' s' ^ T.mult) x)
        (orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x) :=
    orderAt_sup _ _ x
  have hmin := le_trans hx0 (le_of_eq hsup)
  have hxN : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ orderAt (lastNonMonomialPart T' s' ^ T.mult) x := le_trans hmin (min_le_left _ _)
  have hxI : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x := le_trans hmin (min_le_right _ _)
  have hpowI : orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x
      = ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) * orderAt (s'.ideal s'.length) x :=
    orderAt_pow T'.base (s'.proj s'.length ≫ T'.structMap) (s'.ideal s'.length)
      (maxOrderNonMonomialOnOrderLocus T s) x
  have hpowN : orderAt (lastNonMonomialPart T' s' ^ T.mult) x
      = ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x :=
    orderAt_pow T'.base (s'.proj s'.length ≫ T'.structMap) (lastNonMonomialPart T' s') T.mult x
  have hA : ((T.mult : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length) x :=
    natCast_le_of_natCast_mul_le_mul T.mult (maxOrderNonMonomialOnOrderLocus T s) hp1 (orderAt (s'.ideal s'.length) x)
      (le_trans hxI (le_of_eq hpowI))
  have hmultE : ((T'.mult : ℕ) : ℕ∞) = ((T.mult : ℕ) : ℕ∞) := by rw [hmult]
  have hmem : x ∈ orderAtLeastLocus (s'.ideal s'.length) T'.mult :=
    (mem_orderAtLeastLocus_iff _ _ _).2 (hmultE.trans_le hA)
  have hb := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT' s' x hmem
  have hxN2 : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x :=
    le_trans hxN (le_of_eq hpowN)
  have hxN3 : ((maxOrderNonMonomialOnOrderLocus T s * T.mult : ℕ) : ℕ∞)
      ≤ ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x := by
    rw [Nat.mul_comm (maxOrderNonMonomialOnOrderLocus T s) T.mult]
    exact hxN2
  have hC : ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s') x :=
    natCast_le_of_natCast_mul_le_mul (maxOrderNonMonomialOnOrderLocus T s) T.mult hm1 (orderAt (lastNonMonomialPart T' s') x) hxN3
  have hfin : ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomialOnOrderLocus T' s' : ℕ) : ℕ∞) := le_trans hC hb
  have hnat : maxOrderNonMonomialOnOrderLocus T s ≤ maxOrderNonMonomialOnOrderLocus T' s' := by exact_mod_cast hfin
  omega

end FunctorialResolution.EmbeddedResolution

end
