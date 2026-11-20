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

/- English proof (translation)
The claim follows from `MarkedPullbackSquare.orderAt_comap_verticalMap (markedPullbackSquareId g hT) hT hbc.order A y`.
-/
theorem orderAt_comap_of_baseChangeCompatible (hinv : ComapIsoInvariance.{u}) (F : PrincipalizationAssignment.{u}) (n : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (hbc : BaseChangeCompatible hinv F n T g k' q)
    (A : T.scheme.IdealSheafData) (y : ↥Y) :
    orderAt (A.comap g) y = orderAt A (g.base y) :=
  MarkedPullbackSquare.orderAt_comap_verticalMap (markedPullbackSquareId g hT) hT hbc.order A y

/- English proof (translation)
Use `Set.eq_empty_of_subset_empty ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy'` using `(mem_orderAtLeastLocus_iff (T.ideal.comap g) T.mult y).1 hy`. Rewrite `hy'` using `[orderAt_comap_of_baseChangeCompatible hinv F n T hT g k' q hbc T.ideal y]`. Establish `hmem` using `(mem_orderAtLeastLocus_iff T.ideal T.mult _).2 hy'`.

Rewrite `hmem` using `[h]`. Simplify using `only [Set.mem_empty_iff_false] at hmem`.
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

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem transformAt_eq_mk (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    T.transformAt s i =
      MarkedIdealWithBoundary.mk T.base (s.schemeAt i) (s.projectionToBase i ≫ T.structMap) (s.ideal i) T.mult
        (s.boundary i) := rfl

/- English proof (translation)
The claim follows from `hmg.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length le_rfl`.
-/
theorem MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim (hmg : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    krullDimSucc (s.obj s.length) ≤ T.krullDimSucc :=
  hmg.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length le_rfl

/- English proof (translation)
Establish `h` using `hmg.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl`. Rewrite `h` using `[transformAt_eq_mk T s.toMarkedSequenceOfBlowups s.length, toMarkedSequence_projectionToBase s s.length]`. Conclude with `h`.
-/
theorem MonomialGeometryHypotheses.isAdmissible_tripleAtLength (hmg : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible := by
  have h := hmg.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl
  rw [transformAt_eq_mk T s.toMarkedSequenceOfBlowups s.length,
    toMarkedSequence_projectionToBase s s.length] at h
  exact h

/- English proof (translation)
Substitute `hI` using the available equality. Substitute `hm` using the available equality. Conclude with `h`.
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

/- English proof (translation)
Establish `hmg` using `hG.monomialInputs`. Establish `hdimS` using `MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s`. Establish `hvalS` using `MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s`. Establish `hvalS'0` using `MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'`. Establish `hvalS'` using `isAdmissible_mk_congr hlastIdeal hmult hvalS'0`.

Establish `hmain` using `hbc.nonMonomial (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) (s'.boundary s'.length) hsameBoundary.symm hvalS'`. Establish `h0 : lastNonMonomialPart T' s' = nonMonomialPart (s'.boundary s'.length) (s'.ideal s'.length)`. Both sides reduce to the same expression. Establish `h1 : lastNonMonomialPart T s = nonMonomialPart (s.boundary s.length) (s.ideal s.length)` using `rfl`. Rewrite using `[h0, h1, hlastIdeal]`.

Conclude with `hmain`.
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

/- English proof (translation)
Establish `key : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap` using `lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Establish `hvalid : (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.toMarkedSequenceOfBlowups.projectionToSpec s.length) (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible` using `hG.monomialInputs.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl`. Establish `hord : ∀ (J : (s.obj s.length).IdealSheafData) (y : ↥(s'.obj s'.length)), orderAt (J.comap c.lastMap) y = orderAt J (c.lastMap.base y)` using `hbc.order (s.obj s.length) (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length) (s.toMarkedSequenceOfBlowups.projectionToSpec s.length) (s.ideal s.length) (s.boundary s.length) hvalid (MarkedSequenceOfBlowups.projectionToSpec_eq s.toMarkedSequenceOfBlowups …`. Establish `hmain : ∀ y : ↥(s'.obj s'.length), orderAt (lastNonMonomialPart T' s') y ≤ (maxOrderNonMonomial T s : ℕ∞)`. Introduce `y`.

Establish `h1 : orderAt (lastNonMonomialPart T' s') y = orderAt (lastNonMonomialPart T s) (c.lastMap.base y)` using `(congrArg (fun I : (s'.obj s'.length).IdealSheafData => orderAt I y) key).trans (hord (lastNonMonomialPart T s) y)`. Conclude with `le_of_eq_of_le h1 (orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s (c.lastMap.base y))`. Use `show sSup {m : ℕ | ∃ x : ↥(s'.obj s'.length), (m : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s') x} ≤ maxOrderNonMonomial T s`. Use `csSup_le' ?_` and prove the remaining obligations. Introduce `m hm`.

Take `⟨y, hy⟩` from `hm`. Establish `hcast : (m : ℕ∞) ≤ (maxOrderNonMonomial T s : ℕ∞)` using `hy.trans (hmain y)`. Conclude with `hcast` after adjusting the coercions.
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

/- English proof (translation)
Unfold `maxOrderOn`. Use `csSup_le' ?_` and prove the remaining obligations. Introduce `m hmem`. Take `⟨x, hx, hmx⟩` from `hmem`. Conclude with `h m x hx hmx`.
-/
private theorem maxOrderOn_le_of_forall {X : Scheme.{u}} (N : X.IdealSheafData) (S : Set ↥X)
    (K : ℕ) (h : ∀ m : ℕ, ∀ x ∈ S, (m : ℕ∞) ≤ orderAt N x → m ≤ K) :
    maxOrderOn N S ≤ K := by
  unfold maxOrderOn
  refine csSup_le' ?_
  intro m hmem
  obtain ⟨x, hx, hmx⟩ := hmem
  exact h m x hx hmx

/- English proof (translation)
Establish `hmg` using `hG.monomialInputs`. Establish `hdimS` using `MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s`. Establish `hvalS` using `MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s`. Establish `hordLast : ∀ (Aid : (s.obj s.length).IdealSheafData) (y : ↥(s'.obj s'.length)), orderAt (Aid.comap c.lastMap) y = orderAt Aid (c.lastMap.base y)` using `fun Aid y => MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) hT hbc.order Aid y`. Establish `hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap` using `lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`.

Establish `hmain : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderOn (lastNonMonomialPart T' s') (orderAtLeastLocus (s'.ideal s'.length) T'.mult)` using `rfl`. Rewrite using `[hmain]`. Use `maxOrderOn_le_of_forall _ _ _ ?_` and prove the remaining obligations. Introduce `m x' hx' hm`. Establish `hEq1 : orderAt (s'.ideal s'.length) x' = orderAt (s.ideal s.length) (c.lastMap.base x')` using `(congrArg (fun I => orderAt I x') hlastIdeal).trans (hordLast (s.ideal s.length) x')`.

Establish `hEq2 : orderAt (lastNonMonomialPart T' s') x' = orderAt (lastNonMonomialPart T s) (c.lastMap.base x')` using `(congrArg (fun I => orderAt I x') hnonMon).trans (hordLast (lastNonMonomialPart T s) x')`. Establish `h1 : ((T'.mult : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length) x'` using `(mem_orderAtLeastLocus_iff _ _ _).1 hx'`. Establish `hmult' : ((T.mult : ℕ) : ℕ∞) = ((T'.mult : ℕ) : ℕ∞)` using `by rw [hmult]`. Establish `h3 : ((T.mult : ℕ) : ℕ∞) ≤ orderAt (s.ideal s.length) (c.lastMap.base x')` using `hmult'.trans_le (h1.trans_eq hEq1)`. Establish `hxmem : c.lastMap.base x' ∈ orderAtLeastLocus (s.ideal s.length) T.mult` using `(mem_orderAtLeastLocus_iff _ _ _).2 h3`.

Establish `hle` using `orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s (c.lastMap.base x') hxmem`. Establish `hfin : ((m : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)` using `(hm.trans_eq hEq2).trans hle`. Conclude with `hfin` after adjusting the coercions.
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

/- English proof (translation)
Establish `hne : {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}.Nonempty`. Use `⟨0, x₀, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hbdd : BddAbove {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}`. Use `⟨sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}, ?_⟩` and prove the remaining obligations.

Introduce `m hm`. Take `⟨y, hy⟩` from `hm`. Establish `h` using `hy.trans (hbound y)`. Conclude with `h` after adjusting the coercions. Take `⟨y, hy⟩` from `Nat.sSup_mem hne hbdd`.

Conclude with `⟨y, (mem_orderAtLeastLocus_iff N _ y).2 hy⟩`.
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

/- English proof (translation)
Establish `hle : maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s` using `maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Unfold `NonMonomialOrderReductionContinues at hcont ⊢`. Take `⟨h1, h2⟩` from `hcont`. Take `⟨x', -⟩` from `h2`. Rewrite `h1` using `[hmult]`.

Use `⟨le_trans h1 hle, ?_⟩` and prove the remaining obligations. Establish `hbound : ∀ x : ↥(s.obj s.length), orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞)` using `fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x`. Conclude with `orderAtLeastLocus_sSup_nonempty (lastNonMonomialPart T s) (c.lastMap.base x') hbound`.
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

/- English proof (translation)
Establish `hle : maxOrderNonMonomialOnOrderLocus T' s' ≤ maxOrderNonMonomialOnOrderLocus T s` using `maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Unfold `CompanionIdealReductionContinues at hcont ⊢`. Use linear arithmetic over natural numbers and integers.
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

/- English proof (translation)
Simplify using `only [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow]`.
-/
private theorem comap_pow_sup_pow {A B : Scheme.{u}} (f : A ⟶ B) (N J : B.IdealSheafData)
    (a b : ℕ) : (N ^ a ⊔ J ^ b).comap f = (N.comap f) ^ a ⊔ (J.comap f) ^ b := by
  simp only [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow]

/- English proof (translation)
Substitute `h₁` using the available equality. Substitute `h₂` using the available equality. Substitute `ha` using the available equality. Substitute `hb` using the available equality. Conclude with `(comap_pow_sup_pow f N₁ N₂ _ _).symm`.
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

/- English proof (translation)
Establish `hnonMon` using `lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Unfold `companionIdeal`. Conclude with `pow_sup_pow_eq_comap_pow_sup_pow _ _ _ _ _ T'.mult T.mult (maxOrderNonMonomialOnOrderLocus T' s') (maxOrderNonMonomialOnOrderLocus T s) hnonMon hlastIdeal hmult hinveq`.
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

/- English proof (translation)
Establish `h1 : appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) hd)`. Unfold `appendRecursivePrincipalization`. Conclude with `dif_pos hd`. Rewrite using `[h1]`. Unfold `appendIfMarked`.

Rewrite using `[h]`.
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

/- English proof (translation)
Establish `h1 : appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) hd)`. Unfold `appendRecursivePrincipalization`. Conclude with `dif_pos hd`. Rewrite using `[h1]`. Unfold `appendIfMarked`.

Rewrite using `[h]`.
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

/- English proof (translation)
Distinguish the cases in `hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)`. Distinguish the cases in `hm' : (MarkedBlowupSequenceData.ofMarkedSequence σ').IsMarked (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' (s'.boundary s'.length)`. Establish `he : markedDataOfSeq s J μ σ = some ((MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) hm)`. Unfold `markedDataOfSeq`. Conclude with `dif_pos hm`.

Establish `he' : markedDataOfSeq s' K ν σ' = some ((MarkedBlowupSequenceData.ofMarkedSequence σ').toMarkedBlowupSequenceData (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' (s'.boundary s'.length) hm')`. Unfold `markedDataOfSeq`. Conclude with `dif_pos hm'`. Establish `hdd` using `Option.some.inj (hrem.symm.trans he)`. Establish `hdd'` using `Option.some.inj (hrem'.symm.trans he')`.

Substitute `hdd` using the available equality. Substitute `hdd'` using the available equality. Conclude with `⟨SequenceOfBlowupsPullback.toBlowupDataOfSeq cc⟩`. Establish `hnone : markedDataOfSeq s' K ν σ' = none`. Unfold `markedDataOfSeq`.

Conclude with `dif_neg hm'`. Conclude with `absurd (hrem'.symm.trans hnone) (Option.some_ne_none d')`. Establish `hnone : markedDataOfSeq s J μ σ = none`. Unfold `markedDataOfSeq`. Conclude with `dif_neg hm`.

Conclude with `absurd (hrem.symm.trans hnone) (Option.some_ne_none d)`.
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

/- English proof (translation)
Establish `hmg` using `hG.monomialInputs`. Establish `hdimS : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc` using `MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s`. Establish `hdimS'T : krullDimSucc (s'.obj s'.length) ≤ T'.krullDimSucc` using `MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T' hT' s'`. Establish `hdimS'n : krullDimSucc (s'.obj s'.length) ≤ n` using `le_trans hdimS'T hdim'`. Establish `hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc` using `hdimS`.

Establish `hd' : (tripleAtLength T' s' (J.comap c.lastMap) μ).krullDimSucc ≤ T'.krullDimSucc` using `hdimS'T`. Establish `hiff` using `hmark hd hd'`. Consider the cases of `hq : markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) with`. Consider the case `none`. Establish `hq2 : markedDataOfSeq s' (J.comap c.lastMap) μ (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') = none` using `hiff.mp hq`.

Rewrite using `[appendRecursivePrincipalization_eq_self_of_eq_none hinv T (principalizationOfDimLe T A) s J μ hd hq, appendRecursivePrincipalization_eq_self_of_eq_none hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ hd' hq2]`. Conclude with `⟨c⟩`. Consider the case `some d`. Consider the cases of `hq' : markedDataOfSeq s' (J.comap c.lastMap) μ (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') with`. Consider the case `none => exact absurd (hq.symm.trans (hiff.mpr hq')) (Option.some_ne_none d)`.

Consider the case `some d'`. Establish `hrule : IsPullbackBlowupSequence c.lastMap (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd').toSequenceOfBlowups (principalizationOfDimLe T A (tripleAtLength T s J μ) hd).toSequenceOfBlowups` using `hbc.rule (markedPullbackSquareAtLength T T' g s s' c J μ hdimS hJ) hord (s'.boundary s'.length) hsameBoundary.symm hJ' hdimS'n`. Take `⟨cc⟩` from `hrule.nonempty_sequenceOfBlowupsPullback`. Take `⟨e⟩` from `nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq s s' J μ (J.comap c.lastMap) μ c.lastMap (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') d d' hq hq' cc`. Rewrite using `[appendRecursivePrincipalization_eq_append_of_eq_some hinv T (principalizationOfDimLe T A) s J μ hd d hq, appendRecursivePrincipalization_eq_append_of_eq_some hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ hd' d' hq']`.

Conclude with `(isPullbackBlowupSequence_append_of_two_fields g s d s' d' hinv c e).nonempty_sequenceOfBlowupsPullback`.
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

/- English proof (translation)
Both sides reduce to the same expression.
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

/- English proof (translation)
Establish `hval : ∀ l ≤ σ.toSequenceOfBlowups.length, ((tripleAtLength T s J μ).transformAt σ l).IsAdmissible`. Introduce `l hl`. Conclude with `hG.monomialInputs.level_valid (tripleAtLength T s J μ) hJ σ l hl`. Establish `hsub` using `MarkedSequenceOfBlowups.orderAtLeastLocus_subset_preimage_transitionMap (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs) (tripleAtLength T s J μ) σ hval μ le_rfl 0 j (Nat.zero_le j) hj`. Establish `h0 : (σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z ∈ orderAtLeastLocus (σ.ideal 0) μ` using `hsub hz`.

Rewrite `h0` using `[σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero J μ]`. Establish `hcomp : (σ.toSequenceOfBlowups.projectionToBase j).base z = (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z)`. Rewrite using `[SequenceOfBlowups.projectionToBase_def]`. Simplify using the standard rewrite rules. Rewrite using `[hcomp]`.

Conclude with `h0`.
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

/- English proof (translation)
Establish `hdl : (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm).length = σ.toSequenceOfBlowups.length` using `rfl`. Rewrite `hi` using `[MarkedBlowupSequenceData.append_length, hdl]`. Establish `hprojd : ∀ j : ℕ, (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm).proj j = σ.toSequenceOfBlowups.projectionToBase j`. Introduce `j`. Use `Eq.trans (MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) j) ?_` and prove the remaining obligations.

Conclude with `BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups σ.toSequenceOfBlowups j`. Break down `Nat.eq_or_lt_of_le hi₀ with heq | hlt` into its components or cases. Substitute `heq` using the available equality. Establish `hσ0 : 0 < σ.toSequenceOfBlowups.length` using `by omega`. Establish `hz1 : z ∈ ((s.appendToBlowupSequenceData (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)).center s.length).support` using `hz`.

Rewrite `hz1` using `[MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)]`. Establish `hz2` using `AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1`. Establish `hz3` using `AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz2`. Establish `hz4 : (σ.toSequenceOfBlowups.isoZero.inv).base ((eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) (le_refl s.length))).base z) ∈ orderAtLeastLocus (σ.ideal 0) μ` using `σ.center_order 0 hσ0 hz3`. Establish `hx0` using `projectionToBase_mem_orderAtLeastLocus_tripleAtLength hG hinv T s J μ hJ σ 0 (Nat.zero_le _) _ hz4`.

Use `⟨(eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) (le_refl s.length))).base z, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hx0` using `[SequenceOfBlowups.projectionToBase_zero]`. Establish `hcan : ∀ u : ↥(s.obj s.length), (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.isoZero.inv).base u) = u`. Introduce `u`. Simplify using the standard rewrite rules.

Rewrite `hx0` using `[hcan]`. Then use the resulting hypothesis. Rewrite using `[MarkedBlowupSequenceData.append_projectionToBase, MarkedBlowupSequenceData.appendProjectionToBase_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) (le_refl s.length)]`. Conclude with `AlgebraicGeometry.Scheme.Hom.comp_apply _ _ z`. Establish `hkσ : i - s.length < σ.toSequenceOfBlowups.length` using `by omega`. Establish `hz1 : z ∈ ((s.appendToBlowupSequenceData (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)).center i).support` using `hz`.

Rewrite `hz1` using `[MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt]`. Establish `hz2` using `AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1`. Establish `hz3 : ((eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt)).base z) ∈ orderAtLeastLocus (σ.ideal (i - s.length)) μ` using `σ.center_order (i - s.length) hkσ hz2`. Establish `hx0` using `projectionToBase_mem_orderAtLeastLocus_tripleAtLength hG hinv T s J μ hJ σ (i - s.length) (le_of_lt hkσ) _ hz3`. Use `⟨_, hx0, ?_⟩` and prove the remaining obligations.

Rewrite using `[MarkedBlowupSequenceData.append_projectionToBase, MarkedBlowupSequenceData.appendProjectionToBase_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt, hprojd]`. Conclude with `base_comp_comp_apply _ _ _ z`.
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

/- English proof (translation)
Substitute `hD` using the available equality. Take `⟨x, hx, hproj⟩` from `exists_mem_orderAtLeastLocus_of_mem_center_append hG hinv T s J μ hJ σ hm i hi₀ hi z hz`. Introduce `hcon`. Rewrite `hcon` using `[hproj]`. Establish `hsq : IsPullback c.lastMap (s'.proj s'.length) (s.proj s.length) g`.

Establish `h` using `c.isPullback_lastMap`. Rewrite `h` using `[toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase]`. Then use the resulting hypothesis. Take `⟨w, hw, -⟩` from `Scheme.exists_preimage_of_isPullback hsq x y hcon.symm`. Establish `hdimS` using `MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hG.monomialInputs T hT s`. Establish `hvalS` using `MonomialGeometryHypotheses.isAdmissible_tripleAtLength hG.monomialInputs T hT s`.

Establish `hord : orderAt (J.comap c.lastMap) w = orderAt J (c.lastMap.base w)` using `MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) hT hbc.order J w`. Establish `hmem : w ∈ orderAtLeastLocus (J.comap c.lastMap) μ`. Rewrite using `[mem_orderAtLeastLocus_iff, hord, hw]`. Conclude with `(mem_orderAtLeastLocus_iff J μ x).1 hx`. Rewrite `hmem` using `[hempty]`.

Simplify using `only [Set.mem_empty_iff_false] at hmem`.
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

/- English proof (translation)
Distinguish the cases in `hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc`. Distinguish the cases in `hm : (MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T (principalizationOfDimLe T A) s J μ hd)).IsMarked (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)`. Conclude with `append_proj_center_ne_base_of_orderAtLeastLocus_empty hG hinv T T' g hT n A hbc s s' c J μ hJ hempty (principalizationSeqAtEnd T (principalizationOfDimLe T A) s J μ hd) hm (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ) (appendRecursivePrincipalizatio …`. It suffices to derive a contradiction. Establish `hrs : markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) = none`.

Unfold `markedDataOfSeq`. Conclude with `dif_neg hm`. Establish `he : appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ = s` using `appendRecursivePrincipalization_eq_self_of_eq_none hinv T (principalizationOfDimLe T A) s J μ hd hrs`. Rewrite `hi` using `[he]`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Establish `he : appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ = s`. Unfold `appendRecursivePrincipalization`. Conclude with `dif_neg hd`. Rewrite `hi` using `[he]`.

Use linear arithmetic over natural numbers and integers.
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

/- English proof (translation)
Unfold `appendRecursivePrincipalization`. Distinguish the cases in `hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc`. Rewrite using `[dif_pos hd]`. Unfold `appendIfMarked`. Consider the cases of `hrem : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) with`.

Consider the case `none => exact Or.inl rfl`. Consider the case `some d => exact Or.inr ⟨d, rfl⟩`. Rewrite using `[dif_neg hd]`. Conclude with `Or.inl rfl`.
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

/- English proof (translation)
Break down `appendRecursivePrincipalization_eq_self_or_append hinv T (principalizationOfDimLe T A) s J μ with heq | ⟨t, heq⟩` into its components or cases. Rewrite using `[heq]`. Conclude with `⟨c⟩`. Establish `hmiss` using `appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary J μ hJ hempty`. Establish `hconcat : (s.append t hinv).toBlowupSequenceData = s.toBlowupSequenceData.append t.toBlowupSequenceData`.

Rewrite using `[MarkedBlowupSequenceData.append_toBlowupSequenceData]`. Both sides reduce to the same expression. Establish `hseq : (s.append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups = (s.toBlowupSequenceData.append t.toBlowupSequenceData).toSequenceOfBlowups` using `congrArg (fun D : BlowupSequenceData T.scheme => D.toSequenceOfBlowups) hconcat`. Establish `h0 : ∀ i : ℕ, s.length ≤ i → i < (s.append t hinv).length → ∀ z : ↥((s.append t hinv).obj i), z ∈ ((s.append t hinv).center i).support → ∀ y : ↥T'.scheme, g.base y ≠ ((s.append t hinv).proj i).base z`. Rewrite using `[← heq]`.

Conclude with `hmiss`. Establish `h0' : ∀ i : ℕ, s.length ≤ i → i < s.length + t.length → ∀ z : ↥((s.append t hinv).obj i), z ∈ ((s.append t hinv).center i).support → ∀ y : ↥T'.scheme, g.base y ≠ ((s.append t hinv).proj i).base z`. Introduce `i hi0 hi`. Use `h0 i hi0 ?_` and prove the remaining obligations. Rewrite using `[MarkedBlowupSequenceData.append_length]`.

Conclude with `hi`. Establish `hproj : ∀ i : ℕ, (s.append t hinv).toBlowupSequenceData.projectionToBase i = (s.append t hinv).proj i`. Introduce `i`. Rewrite using `[MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups]`. Conclude with `(BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s.append t hinv).toBlowupSequenceData i).symm`.

Establish `key : ∀ i : ℕ, s.toBlowupSequenceData.length ≤ i → i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length → ∀ z : ↥((s.toBlowupSequenceData.append t.toBlowupSequenceData).obj i), z ∈ ((s.toBlowupSequenceData.append t.toBlowupSequenceData).center i).support → ∀ y : ↥T'. …`. Rewrite using `[← hconcat]`. Introduce `i hi0 hi z hz y`. Rewrite using `[hproj i]`. Conclude with `h0' i hi0 hi z hz y`.

Rewrite using `[heq, hseq]`. Conclude with `SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers g s'.toBlowupSequenceData s.toBlowupSequenceData t.toBlowupSequenceData c key`.
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

/- English proof (translation)
Establish `hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap` using `lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Establish `hJ : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).IsAdmissible` using `isAdmissible_nonMonomialTriple hG hT s hcont`. Establish `hJ' : (tripleAtLength T' s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s')).IsAdmissible` using `isAdmissible_nonMonomialTriple hG hT' s' hcont'`. Rewrite `hJ'` using `[hnonMon, hinveq]`. Establish `hord : ∀ x : ↥(s.obj s.length), orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞)` using `fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x`.

Establish `key` using `nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lastNonMonomialPart T s) (maxOrderNonMonomial T s) hJ hJ' hord hmark`. Establish `hL : extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)` using `rfl`. Establish `hU : extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s' = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s')` using `rfl`. Rewrite `hU` using `[hnonMon, hinveq]`. Rewrite using `[hL, hU]`.

Conclude with `key`.
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

/- English proof (translation)
Substitute `hJK` using the available equality. Substitute `hμν` using the available equality. Both sides reduce to the same expression.
-/
private theorem appendRecursivePrincipalization_congr (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν) :
    appendRecursivePrincipalization hinv T rc s J μ = appendRecursivePrincipalization hinv T rc s K ν := by
  subst hJK
  subst hμν
  rfl

/- English proof (translation)
Substitute `hJK` using the available equality. Substitute `hμν` using the available equality. Conclude with `h`.
-/
private theorem isAdmissible_tripleAtLength_congr (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν)
    (h : (tripleAtLength T s J μ).IsAdmissible) : (tripleAtLength T s K ν).IsAdmissible := by
  subst hJK
  subst hμν
  exact h

/- English proof (translation)
Establish `hJideal : companionIdeal T' s' = (companionIdeal T s).comap c.lastMap` using `companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hinveq`. Establish `hmu : T'.mult * maxOrderNonMonomialOnOrderLocus T' s' = T.mult * maxOrderNonMonomialOnOrderLocus T s`. Rewrite using `[hinveq, hmult]`. Establish `hJ : (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)).IsAdmissible` using `companionTriple_isAdmissible hG hT s hcont`. Establish `hJ'0 : (tripleAtLength T' s' (companionIdeal T' s') (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')).IsAdmissible` using `companionTriple_isAdmissible hG hT' s' hcont'`.

Establish `hJ' : (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap) (T.mult * maxOrderNonMonomialOnOrderLocus T s)).IsAdmissible` using `isAdmissible_tripleAtLength_congr T' s' (companionIdeal T' s') ((companionIdeal T s).comap c.lastMap) (T'.mult * maxOrderNonMonomialOnOrderLocus T' s') (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu hJ'0`. Establish `hord` using `orderAt_companionIdeal_le hG hT s hcont`. Establish `hA : extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)` using `rfl`. Establish `hB0 : extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s' = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (companionIdeal T' s') (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')` using `rfl`. Establish `hB : extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s' = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' ((companionIdeal T s).comap c.lastMap) (T.mult * maxOrderNonMonomialOnOrderLocus T s)` using `hB0.trans (appendRecursivePrincipalization_congr hinv T' (principalizationOfDimLe T' A) s' (companionIdeal T' s') ((companionIdeal T s).comap c.lastMap) (T'.mult * maxOrderNonMonomialOnOrderLocus T' s') (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu)`.

Rewrite using `[hA, hB]`. Conclude with `nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJ hJ' hord hmark`.
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

/- English proof (translation)
Establish `hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap` using `lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Use `Set.eq_empty_of_subset_empty ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy'` using `(mem_orderAtLeastLocus_iff ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) y).1 hy`. Rewrite `hy'` using `[← hnonMon]`.

Establish `hle : orderAt (lastNonMonomialPart T' s') y ≤ ((maxOrderNonMonomial T' s' : ℕ) : ℕ∞)` using `orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT' s' y`. Establish `hcast : ((maxOrderNonMonomial T s : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomial T' s' : ℕ) : ℕ∞)` using `hy'.trans hle`. Establish `hnat : maxOrderNonMonomial T s ≤ maxOrderNonMonomial T' s'` using `by exact_mod_cast hcast`. Conclude with `absurd hnat (not_le.mpr hlt)`.
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

/- English proof (translation)
Break down `eq_or_ne a ⊤ with rfl | ha` into its components or cases. Conclude with `le_top`. Take `⟨a₀, rfl⟩` from `ENat.ne_top_iff_exists.mp ha`. Establish `h' : m * p ≤ p * a₀` using `by exact_mod_cast h`. Establish `h'' : p * m ≤ p * a₀`.

Rewrite using `[Nat.mul_comm p m]`. Conclude with `h'`. Establish `hle : m ≤ a₀` using `Nat.le_of_mul_le_mul_left h'' (by omega)`. Conclude with `hle` after adjusting the coercions.
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

/- English proof (translation)
Establish `hmg` using `hG.monomialInputs`. Establish `hvalS'` using `MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'`. Establish `hchar : CharZero T'.base` using `hvalS'.charZero`. Establish `hsmooth : AlgebraicGeometry.Smooth (s'.proj s'.length ≫ T'.structMap)` using `hvalS'.smooth`. Establish `hm1 : 1 ≤ T.mult` using `hT.one_le_mult`.

Establish `hp1 : 1 ≤ maxOrderNonMonomialOnOrderLocus T s` using `by omega`. Establish `hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap` using `lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary`. Establish `hcompanion : (companionIdeal T s).comap c.lastMap = lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s`. Unfold `companionIdeal`. Rewrite using `[hnonMon, hlastIdeal]`.

Conclude with `comap_pow_sup_pow c.lastMap (lastNonMonomialPart T s) (s.ideal s.length) T.mult (maxOrderNonMonomialOnOrderLocus T s)`. Rewrite using `[hcompanion]`. Use `Set.eq_empty_of_subset_empty ?_` and prove the remaining obligations. Introduce `x hx`. It suffices to derive a contradiction.

Establish `hx0 : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x` using `(mem_orderAtLeastLocus_iff _ _ _).1 hx`. Establish `hsup : orderAt (lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x = min (orderAt (lastNonMonomialPart T' s' ^ T.mult) x) (orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x)` using `orderAt_sup _ _ x`. Establish `hmin` using `le_trans hx0 (le_of_eq hsup)`. Establish `hxN : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s' ^ T.mult) x` using `le_trans hmin (min_le_left _ _)`. Establish `hxI : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x` using `le_trans hmin (min_le_right _ _)`.

Establish `hpowI : orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x = ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) * orderAt (s'.ideal s'.length) x` using `orderAt_pow T'.base (s'.proj s'.length ≫ T'.structMap) (s'.ideal s'.length) (maxOrderNonMonomialOnOrderLocus T s) x`. Establish `hpowN : orderAt (lastNonMonomialPart T' s' ^ T.mult) x = ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x` using `orderAt_pow T'.base (s'.proj s'.length ≫ T'.structMap) (lastNonMonomialPart T' s') T.mult x`. Establish `hA : ((T.mult : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length) x` using `natCast_le_of_natCast_mul_le_mul T.mult (maxOrderNonMonomialOnOrderLocus T s) hp1 (orderAt (s'.ideal s'.length) x) (le_trans hxI (le_of_eq hpowI))`. Establish `hmultE : ((T'.mult : ℕ) : ℕ∞) = ((T.mult : ℕ) : ℕ∞)` using `by rw [hmult]`. Establish `hmem : x ∈ orderAtLeastLocus (s'.ideal s'.length) T'.mult` using `(mem_orderAtLeastLocus_iff _ _ _).2 (hmultE.trans_le hA)`.

Establish `hb` using `orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT' s' x hmem`. Establish `hxN2 : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x` using `le_trans hxN (le_of_eq hpowN)`. Establish `hxN3 : ((maxOrderNonMonomialOnOrderLocus T s * T.mult : ℕ) : ℕ∞) ≤ ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x`. Rewrite using `[Nat.mul_comm (maxOrderNonMonomialOnOrderLocus T s) T.mult]`. Conclude with `hxN2`.

Establish `hC : ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s') x` using `natCast_le_of_natCast_mul_le_mul (maxOrderNonMonomialOnOrderLocus T s) T.mult hm1 (orderAt (lastNonMonomialPart T' s') x) hxN3`. Establish `hfin : ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomialOnOrderLocus T' s' : ℕ) : ℕ∞)` using `le_trans hC hb`. Establish `hnat : maxOrderNonMonomialOnOrderLocus T s ≤ maxOrderNonMonomialOnOrderLocus T' s'` using `by exact_mod_cast hfin`. Use linear arithmetic over natural numbers and integers.
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
