import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BoundaryDeletion

/- English proof (authored)
Since the index is in range, the tail beginning there consists of the entry at that index followed by the tail after it. Prepending the initial segment reconstructs the whole list.
-/
private theorem take_append_getElem_cons_drop {α : Type v} (L : List α) (i : ℕ)
    (h : i < L.length) : L.take i ++ L[i] :: L.drop (i + 1) = L := by
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

/- English proof (authored)
Substitute the equality of the second boundary lists. The given relation then applies to the required pair.
-/
private theorem sameNontrivialBoundary_congr_right {X : Scheme.{u}} (L₁ L₂ L₂' : List X.IdealSheafData)
    (h : L₂ = L₂') (hbe : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₂ := by
  subst h
  exact hbe

/- English proof (authored)
Identify each list with its equal list in the given relation. The same nontrivial boundary condition immediately transfers to the original pair.
-/
private theorem sameNontrivialBoundary_congr {X : Scheme.{u}} (L₁ L₁' L₂ L₂' : List X.IdealSheafData)
    (h₁ : L₁ = L₁') (h₂ : L₂ = L₂') (hbe : MarkedIdealWithBoundary.SameNontrivialBoundary L₁' L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₂ := by
  subst h₁
  subst h₂
  exact hbe

/- English proof (authored)
Substitute the equality of the source sequences into the given pullback relation.
-/
private theorem isPullback_congr {X₀ Y₀ : Scheme.{u}} (φ : Y₀ ⟶ X₀) (sbase : SequenceOfBlowups X₀)
    {t₁ t₂ : SequenceOfBlowups Y₀} (h : t₁ = t₂) (hp : IsPullbackBlowupSequence φ t₁ sbase) :
    IsPullbackBlowupSequence φ t₂ sbase := by
  subst h
  exact hp

/- English proof (authored)
Identify the triples, so the two comparison maps have the same source and the equality of maps applies there. The assignment gives the same sequence on the common triple. After the two identifications the existing pullback relation is the required one.
-/
private theorem isPullback_congr_marked (F : PrincipalizationAssignment.{u}) {X₀ : Scheme.{u}}
    (sbase : SequenceOfBlowups X₀) {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂)
    (φ₁ : T₁.scheme ⟶ X₀) (φ₂ : T₂.scheme ⟶ X₀) (hφ : HEq φ₁ φ₂)
    (hp : IsPullbackBlowupSequence φ₁ (F T₁).toSequenceOfBlowups sbase) :
    IsPullbackBlowupSequence φ₂ (F T₂).toSequenceOfBlowups sbase := by
  subst h
  have hee : φ₁ = φ₂ := eq_of_heq hφ
  subst hee
  exact hp

/- English proof (authored)
An equality of marked triples identifies their component data and hence their admissibility conditions. Transfer the given certificate along it.
-/
private theorem isAdmissible_of_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂) (hv : T₂.IsAdmissible) :
    T₁.IsAdmissible := by
  subst h
  exact hv

/- English proof (authored)
Equal triples have the same underlying scheme and successor dimension. The given dimension predicate therefore holds for the first triple.
-/
private theorem pred_dim_of_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂) (P : ℕ → Prop)
    (hp : P T₂.krullDimSucc) : P T₁.krullDimSucc := by
  subst h
  exact hp

/- English proof (authored)
Equal triples have the same ideal and mark, so the given pointwise order bound applies to either one.
-/
private theorem isOrderBoundedByMult_of_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂)
    (ho : T₂.IsOrderBoundedByMult) : T₁.IsOrderBoundedByMult := by
  subst h
  exact ho

/- English proof (authored)
The two structural maps coincide after identifying the triples, so local finite type transfers to the first structural map.
-/
private theorem locallyOfFiniteType_of_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂)
    (h₂ : AlgebraicGeometry.LocallyOfFiniteType T₂.structMap) :
    AlgebraicGeometry.LocallyOfFiniteType T₁.structMap := by
  subst h
  exact h₂

/- English proof (authored)
The two tuples of data defining balance agree after identifying the triples. The certificates of local finite type witness the same property, so the given balance condition transfers.
-/
private theorem isBalanced_of_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂)
    (h₁ : AlgebraicGeometry.LocallyOfFiniteType T₁.structMap)
    (h₂ : AlgebraicGeometry.LocallyOfFiniteType T₂.structMap)
    (hd : T₂.IsBalanced h₂) : T₁.IsBalanced h₁ := by
  subst h
  exact hd

/- English proof (authored)
The boundary-position invariance property compares the reductions at the distinguished component, since the two prefixes and the two suffixes agree after ignoring unit entries. The given lengths identify the reduction indices with the two prefix lengths. Transport the existing pullback relation through the resulting isomorphism of source reductions.
-/
private theorem isPullback_of_sameNontrivialBoundary
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (j c : ℕ)
    (hshift : IsBoundaryPositionInvariant P A)
    (W : MarkedIdealWithBoundary.{u}) (hWP : P W.krullDimSucc) (hWO : W.IsOrderBoundedByMult)
    (hftW : AlgebraicGeometry.LocallyOfFiniteType W.structMap) (hWD : W.IsBalanced hftW)
    (E₁ E₂ E₁' E₂' : List W.scheme.IdealSheafData) (Dv : W.scheme.IdealSheafData)
    (hBE₁ : MarkedIdealWithBoundary.SameNontrivialBoundary E₁ E₁')
    (hBE₂ : MarkedIdealWithBoundary.SameNontrivialBoundary E₂ E₂')
    (hlen : E₁.length = j) (hlen' : E₁'.length = c)
    (hV1 : (W.withBoundary (E₁ ++ Dv :: E₂)).IsAdmissible)
    (hV2 : (W.withBoundary (E₁' ++ Dv :: E₂')).IsAdmissible)
    {X₀ : Scheme.{u}} (φ : (W.withBoundary (E₁ ++ Dv :: E₂)).scheme ⟶ X₀)
    (sbase : SequenceOfBlowups X₀)
    (hpull : IsPullbackBlowupSequence φ (A j (W.withBoundary (E₁ ++ Dv :: E₂))).toSequenceOfBlowups sbase) :
    IsPullbackBlowupSequence φ (A c (W.withBoundary (E₁' ++ Dv :: E₂'))).toSequenceOfBlowups sbase := by
  have hEq := hshift.shift W hWP hWO hftW hWD E₁ E₂ E₁' E₂' Dv hBE₁ hBE₂ hV1 hV2
  rw [hlen, hlen'] at hEq
  exact IsPullbackBlowupSequence.of_isomorphic hpull hEq

/- English proof (authored)
Pulling back the original boundary preserves its length and identifies the distinguished entry with the corresponding entry in the modified boundary. Since the modified triple is admissible and the two full lists have the same nontrivial entries, the unmodified pullback triple is also admissible. Its dimension, order, and balance conditions are unchanged by the replacement of the boundary. Apply smooth functoriality of divisor reduction to this unmodified pullback at the original index. Split both lists at the common distinguished entry. Their prefixes and suffixes have the same nontrivial entries by hypothesis, and their prefix lengths give the desired two indices. Boundary-position invariance transports the pullback relation to the reduction for the modified list.
-/
private theorem isPullbackBlowupSequence_pullbackAlong
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u}) (j c : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl) (hshift : IsBoundaryPositionInvariant P A)
    (V : MarkedIdealWithBoundary.{u}) (hVv : V.IsAdmissible) (hP : P V.krullDimSucc) (hO : V.IsOrderBoundedByMult)
    (hftV : AlgebraicGeometry.LocallyOfFiniteType V.structMap) (hDb : V.IsBalanced hftV)
    (Y : Scheme.{u}) (qy : Y ⟶ Spec (CommRingCat.of V.base)) (hmap : Y ⟶ V.scheme)
    (hsm : AlgebraicGeometry.Smooth hmap) (hqy : hmap ≫ V.structMap = qy)
    (LT : List Y.IdealSheafData)
    (hVv' : ((V.pullbackAlong Y qy hmap).withBoundary LT).IsAdmissible)
    (hP' : P ((V.pullbackAlong Y qy hmap).withBoundary LT).krullDimSucc)
    (hO' : ((V.pullbackAlong Y qy hmap).withBoundary LT).IsOrderBoundedByMult)
    (hftV' : AlgebraicGeometry.LocallyOfFiniteType
      ((V.pullbackAlong Y qy hmap).withBoundary LT).structMap)
    (hDb' : ((V.pullbackAlong Y qy hmap).withBoundary LT).IsBalanced hftV')
    (Lbd : List V.scheme.IdealSheafData) (hLbd : V.boundary = Lbd)
    (hjLbd : j < Lbd.length) (hcLT : c < LT.length)
    (hget : (Lbd[j]'hjLbd).comap hmap = LT[c]'hcLT)
    (hfull : MarkedIdealWithBoundary.SameNontrivialBoundary (Lbd.map (fun D => D.comap hmap)) LT)
    (hpre : MarkedIdealWithBoundary.SameNontrivialBoundary ((Lbd.take j).map (fun D => D.comap hmap)) (LT.take c))
    (hsuf : MarkedIdealWithBoundary.SameNontrivialBoundary ((Lbd.drop (j + 1)).map (fun D => D.comap hmap))
      (LT.drop (c + 1))) :
    IsPullbackBlowupSequence hmap (A c ((V.pullbackAlong Y qy hmap).withBoundary LT)).toSequenceOfBlowups
      (A j V).toSequenceOfBlowups := by
  have := hsm
  have hPBb : (V.pullbackAlong Y qy hmap).boundary = Lbd.map (fun D => D.comap hmap) :=
    (MarkedIdealWithBoundary.pullbackAlong_boundary V Y qy hmap).trans
      (congrArg (List.map (fun D => D.comap hmap)) hLbd)
  have hjV : j < V.boundary.length := by
    rw [hLbd]
    exact hjLbd
  have hmaplen : (Lbd.map (fun D => D.comap hmap)).length = Lbd.length := by simp
  have hlenPB : (V.pullbackAlong Y qy hmap).boundary.length = Lbd.length := by
    rw [hPBb]
    exact hmaplen
  have hjPB : j < (V.pullbackAlong Y qy hmap).boundary.length := by
    rw [hlenPB]
    exact hjLbd
  have hPW : P (V.pullbackAlong Y qy hmap).krullDimSucc := hP'
  have hOW : (V.pullbackAlong Y qy hmap).IsOrderBoundedByMult := hO'
  have hftW : AlgebraicGeometry.LocallyOfFiniteType (V.pullbackAlong Y qy hmap).structMap := hftV'
  have hDW : (V.pullbackAlong Y qy hmap).IsBalanced hftW := hDb'
  have hLTbe : MarkedIdealWithBoundary.SameNontrivialBoundary LT (V.pullbackAlong Y qy hmap).boundary :=
    sameNontrivialBoundary_congr_right LT (V.pullbackAlong Y qy hmap).boundary
      (Lbd.map (fun D => D.comap hmap)) hPBb hfull.symm
  have hPBV : (V.pullbackAlong Y qy hmap).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary ((V.pullbackAlong Y qy hmap).withBoundary LT)
      (V.pullbackAlong Y qy hmap).boundary hVv' hLTbe
  have hsplit : (Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
        :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap) = Lbd.map (fun D => D.comap hmap) := by
    rw [← hget]
    have h := congrArg (fun L : List V.scheme.IdealSheafData => L.map (fun D => D.comap hmap))
      (take_append_getElem_cons_drop Lbd j hjLbd)
    simpa only [List.map_append, List.map_cons] using h
  have hsplitLT : LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1) = LT :=
    take_append_getElem_cons_drop LT c hcLT
  have hPBself : (V.pullbackAlong Y qy hmap).withBoundary
        ((Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
          :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap)) = V.pullbackAlong Y qy hmap :=
    (congrArg (MarkedIdealWithBoundary.withBoundary (V.pullbackAlong Y qy hmap))
      (hsplit.trans hPBb.symm)).trans (MarkedIdealWithBoundary.withBoundary_self _)
  have hPBeq : (V.pullbackAlong Y qy hmap).withBoundary
        (LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1))
      = (V.pullbackAlong Y qy hmap).withBoundary LT :=
    congrArg (MarkedIdealWithBoundary.withBoundary (V.pullbackAlong Y qy hmap)) hsplitLT
  have hpullPB := hspec.isPullbackBlowupSequence_of_smooth V hVv hP hO hDb hjV Y qy hmap hqy hPBV hPW hOW hDW hjPB
  have hpull1 : IsPullbackBlowupSequence hmap
      (A j ((V.pullbackAlong Y qy hmap).withBoundary
        ((Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
          :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap)))).toSequenceOfBlowups
      (A j V).toSequenceOfBlowups :=
    isPullback_congr hmap (A j V).toSequenceOfBlowups
      (eq_of_heq ((A j).toSequenceOfBlowups_heq_of_eq hPBself.symm)) hpullPB
  have hV1 : ((V.pullbackAlong Y qy hmap).withBoundary
      ((Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
        :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap))).IsAdmissible := by
    rw [hPBself]
    exact hPBV
  have hV2 : ((V.pullbackAlong Y qy hmap).withBoundary
      (LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1))).IsAdmissible := by
    rw [hPBeq]
    exact hVv'
  have hlenE1 : ((Lbd.take j).map (fun D => D.comap hmap)).length = j := by
    simp only [List.length_map, List.length_take]
    omega
  have hlenE1' : (LT.take c).length = c := by
    simp only [List.length_take]
    omega
  have hres := isPullback_of_sameNontrivialBoundary P A j c hshift (V.pullbackAlong Y qy hmap) hPW hOW hftW hDW
    ((Lbd.take j).map (fun D => D.comap hmap)) ((Lbd.drop (j + 1)).map (fun D => D.comap hmap))
    (LT.take c) (LT.drop (c + 1)) (LT[c]'hcLT) hpre hsuf hlenE1 hlenE1' hV1 hV2 hmap
    (A j V).toSequenceOfBlowups hpull1
  exact isPullback_congr hmap (A j V).toSequenceOfBlowups
    (eq_of_heq ((A c).toSequenceOfBlowups_heq_of_eq hPBeq)) hres

variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u}) (j : ℕ)
  (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
  (Dt : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
  (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
  (hftT : AlgebraicGeometry.LocallyOfFiniteType
    (s'.proj s'.length ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap))

/- English proof (authored)
The smooth final-stage comparison identifies the derived triple upstairs with the pullback of the downstairs derived triple equipped with the final upstairs boundary. Both triples have the needed order bounds and are balanced by tuning. The final boundaries retain the indices from the original lists, and the distinguished component corresponds to the index counting the preceding surviving components upstairs. The comparison of final boundaries matches the whole lists after removing unit ideals and also matches the prefixes before the distinguished entry and through it. Cancel the latter prefixes to match the suffixes. The smooth pullback comparison with a change of boundary position now applies to the derived triple downstairs and the identified triple upstairs.
-/
theorem isPullbackBlowupSequence_derivedTriple
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hj : j < S.boundary.length)
    (hlive : (S.boundary[j]'hj).comap q ≠ ⊤)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS [] 0).IsAdmissible)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).IsAdmissible) :
    IsPullbackBlowupSequence Dt.lastMap
      (A (NontrivialBoundary.survivingBoundaryCount S q j)
        (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0)).toSequenceOfBlowups
      (A j (MaxContactCoverData.derivedTriple S s hftS [] 0)).toSequenceOfBlowups := by
  classical
  have hflatq : AlgebraicGeometry.Flat q := inferInstance
  have hSmoothLast : AlgebraicGeometry.Smooth Dt.lastMap := Dt.smooth_lastMap
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) := by
    have hsmU := hVU.smooth
    rwa [LowerDimReductionPullback.structureMorphism_derivedTriple] at hsmU
  have hpb0 := NontrivialBoundary.pullbackAlong_derivedTriple_eq S q s s' Dt hstar hV hV' hftS hftT hsm [] 0 0
  have hOU := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS [] 0 hVU
  have hDU := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS [] 0 hVU
  have hOU' := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    hftT [] 0 hVU'
  have hDU' := LowerDimReductionPullback.isBalanced_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    hftT [] 0 hVU'
  have hUb : (MaxContactCoverData.derivedTriple S s hftS [] 0).boundary = s.boundary s.length := by
    simp
  have hjL : j < (s.boundary s.length).length :=
    lt_of_lt_of_le hj (NontrivialBoundary.length_boundary_le_length_lastBoundary S s)
  have hcLT : NontrivialBoundary.survivingBoundaryCount S q j < (s'.boundary s'.length).length :=
    lt_of_lt_of_le (NontrivialBoundary.survivingBoundaryCount_lt_length S q j hj hlive)
      (NontrivialBoundary.length_boundary_le_length_lastBoundary (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s')
  have hget : ((s.boundary s.length)[j]'hjL).comap Dt.lastMap
      = (s'.boundary s'.length)[NontrivialBoundary.survivingBoundaryCount S q j]'hcLT :=
    NontrivialBoundary.getElem_lastBoundary_comap_lastMap S q s s' Dt hstar hV hV' j hj hlive
  have hfull : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((s.boundary s.length).map (fun D => D.comap Dt.lastMap)) (s'.boundary s'.length) :=
    ((NontrivialBoundary.ideal_and_boundary_comap_lastMap S q s s' Dt hstar hV hV').2).symm
  have hpre : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((s.boundary s.length).take j).map (fun D => D.comap Dt.lastMap))
      ((s'.boundary s'.length).take (NontrivialBoundary.survivingBoundaryCount S q j)) :=
    NontrivialBoundary.sameNontrivialBoundary_lastBoundary_take S q s s' Dt hstar hV hV' j (le_of_lt hj)
  have hpre1 : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((s.boundary s.length).take (j + 1)).map (fun D => D.comap Dt.lastMap))
      ((s'.boundary s'.length).take (NontrivialBoundary.survivingBoundaryCount S q j + 1)) := by
    have hh := NontrivialBoundary.sameNontrivialBoundary_lastBoundary_take S q s s' Dt hstar hV hV' (j + 1) hj
    rwa [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hj hlive] at hh
  have hmapsplit : ((s.boundary s.length).take (j + 1)).map (fun D => D.comap Dt.lastMap)
        ++ ((s.boundary s.length).drop (j + 1)).map (fun D => D.comap Dt.lastMap)
      = (s.boundary s.length).map (fun D => D.comap Dt.lastMap) := by
    rw [← List.map_append, List.take_append_drop]
  have hltsplit : (s'.boundary s'.length).take (NontrivialBoundary.survivingBoundaryCount S q j + 1)
        ++ (s'.boundary s'.length).drop (NontrivialBoundary.survivingBoundaryCount S q j + 1)
      = s'.boundary s'.length := List.take_append_drop _ _
  have happ := sameNontrivialBoundary_congr _ _ _ _ hmapsplit hltsplit hfull
  have hsuf := NontrivialBoundary.sameNontrivialBoundary_cancel_left happ hpre1
  have hVW' := isAdmissible_of_eq hpb0 hVU'
  have hPW' := pred_dim_of_eq hpb0 P hPU'
  have hOW' := isOrderBoundedByMult_of_eq hpb0 hOU'
  have hftW' := locallyOfFiniteType_of_eq hpb0 hVU'.locallyOfFiniteType
  have hDW' := isBalanced_of_eq hpb0 hftW' hVU'.locallyOfFiniteType hDU'
  have hinner := isPullbackBlowupSequence_pullbackAlong P A Bl j (NontrivialBoundary.survivingBoundaryCount S q j) hspec hshift
    (MaxContactCoverData.derivedTriple S s hftS [] 0) hVU hPU hOU hVU.locallyOfFiniteType hDU
    (s'.obj s'.length) (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [] 0).structMap)
    Dt.lastMap hSmoothLast rfl (s'.boundary s'.length)
    hVW' hPW' hOW' hftW' hDW'
    (s.boundary s.length) hUb hjL hcLT hget hfull hpre hsuf
  exact isPullback_congr_marked (A (NontrivialBoundary.survivingBoundaryCount S q j))
    (A j (MaxContactCoverData.derivedTriple S s hftS [] 0)).toSequenceOfBlowups hpb0 Dt.lastMap Dt.lastMap
    HEq.rfl hinner

include Dt in
/- English proof (authored)
The two distinguished indices are in range in the corresponding final boundaries. The hypotheses allow the append formula on both sides, with no dropped boundary entries to check. It expresses each reduction as the given sequence followed by its marked continuation. The derived-triple comparison gives a pullback relation for the continuations over the final-stage map. Regard it as a comparison of their underlying blowup data and append it to the given comparison of the initial sequences over the original base map.
-/
theorem isPullbackBlowupSequence_appendLowerDimReduction
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hspec' : IsBoundaryDivisorReduction P (NontrivialBoundary.survivingBoundaryCount S q j)
      (A (NontrivialBoundary.survivingBoundaryCount S q j)) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hj : j < S.boundary.length)
    (hlive : (S.boundary[j]'hj).comap q ≠ ⊤)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS [] 0).IsAdmissible)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).IsAdmissible)
    (hdimU : (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc ≤ T.krullDimSucc)
    (hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc ≤ T.krullDimSucc) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [] 0 (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S s [] 0
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hjb : j < ((([] : List (s.obj s.length).IdealSheafData))
      ++ List.drop 0 (s.boundary s.length)).length := by
    simpa using lt_of_lt_of_le hj (NontrivialBoundary.length_boundary_le_length_lastBoundary S s)
  have hjb' : NontrivialBoundary.survivingBoundaryCount S q j <
      ((([] : List (s'.obj s'.length).IdealSheafData))
        ++ List.drop 0 (s'.boundary s'.length)).length := by
    simpa using lt_of_lt_of_le (NontrivialBoundary.survivingBoundaryCount_lt_length S q j hj hlive)
      (NontrivialBoundary.length_boundary_le_length_lastBoundary (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s')
  obtain ⟨hmk, hEq, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl j hspec
    (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl) S hV hm hO s [] 0 hftS hdimU hPU hVU hjb (by simp)
  obtain ⟨hmk', hEq', -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl
    (NontrivialBoundary.survivingBoundaryCount S q j) hspec' (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl)
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s' [] 0 hftT hdimU' hPU' hVU' hjb' (by simp)
  rw [hEq, hEq']
  refine isPullbackBlowupSequence_append_same_field q s _ s' _ hinv Dt ?_
  exact SequenceOfBlowupsPullback.toBlowupDataOfSeq
    (IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback
      (isPullbackBlowupSequence_derivedTriple (P := P) (A := A) (Bl := Bl) (j := j) (S := S) (q := q)
        (s := s) (s' := s') (Dt := Dt) (hftS := hftS) (hftT := hftT) (hstar := hstar)
        (hspec := hspec) (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO)
        (hO' := hO') (hj := hj) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU')
        (hVU' := hVU'))).some

include Dt in
def continuationComparison
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hspec' : IsBoundaryDivisorReduction P (NontrivialBoundary.survivingBoundaryCount S q j)
      (A (NontrivialBoundary.survivingBoundaryCount S q j)) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hj : j < S.boundary.length)
    (hlive : (S.boundary[j]'hj).comap q ≠ ⊤)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS [] 0).IsAdmissible)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).IsAdmissible)
    (hdimU : (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc ≤ T.krullDimSucc)
    (hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc ≤ T.krullDimSucc) :
    SequenceOfBlowupsPullback q
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [] 0 (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S s [] 0 j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback
    (isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (j := j) (S := S) (q := q)
      (s := s) (s' := s') (Dt := Dt) (hftS := hftS) (hftT := hftT)
      (hinv := hinv) (T := T) (hstar := hstar) (hspec := hspec) (hspec' := hspec')
      (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
      (hj := hj) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
      (hdimU := hdimU) (hdimU' := hdimU'))).some

end BoundaryDeletion

end FunctorialResolution.EmbeddedResolution

end
