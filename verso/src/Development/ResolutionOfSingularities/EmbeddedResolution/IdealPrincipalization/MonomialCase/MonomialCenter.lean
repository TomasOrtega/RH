import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The closure of the component is irreducible and lies in the closed support of the intersection ideal. It contains the component, so maximality makes it equal to the component. The component is therefore closed.
-/
theorem isClosed_intersectionComponents_of_mem {Y : Scheme.{u}} {L : List Y.IdealSheafData}
    {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  have h : IsIrreducibleComponentOf C (↑(intersectionIdeal L J).support : Set ↥Y) :=
    (mem_intersectionComponents_iff L J C).1 hC
  have hclosed : IsClosed (↑(intersectionIdeal L J).support : Set ↥Y) :=
    (intersectionIdeal L J).support.2
  have hcl : closure C = C :=
    h.2.2 (closure C) h.1.closure subset_closure (closure_minimal h.2.1 hclosed)
  exact isClosed_of_closure_subset hcl.subset

/- English proof (authored)
An intersection component is a maximal irreducible subset of the intersection support. Irreducibility is part of this condition.
-/
theorem isIrreducible_of_mem_intersectionComponents {Y : Scheme.{u}} {L : List Y.IdealSheafData}
    {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) : IsIrreducible C :=
  ((mem_intersectionComponents_iff L J C).1 hC).1

/- English proof (authored)
The chosen point for the irreducible set has singleton closure equal to the closure of the set. The intersection component is already closed, so this singleton closure is the component itself.
-/
theorem isGenericPoint_genericPoint_of_mem_intersectionComponents {Y : Scheme.{u}}
    {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} {C : Set ↥Y}
    (hC : C ∈ intersectionComponents L J) :
    IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC).genericPoint C := by
  have hcl : closure C = C := (isClosed_intersectionComponents_of_mem hC).closure_eq
  have h : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = closure C := by
    simp
  exact h.trans hcl

/- English proof (authored)
The component is irreducible. The definition of order along an irreducible set gives the order at its generic point.
-/
theorem orderAlong_eq_orderAt_of_mem_intersectionComponents {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} {C : Set ↥Y}
    (hC : C ∈ intersectionComponents L J) :
    orderAlong I C = orderAt I (isIrreducible_of_mem_intersectionComponents hC).genericPoint := by
  unfold orderAlong
  exact dif_pos (isIrreducible_of_mem_intersectionComponents hC)

/- English proof (authored)
With irreducibility supplied, the order-along definition selects the branch evaluating the ideal's order at the generic point.
-/
theorem orderAlong_eq_orderAt_genericPoint {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {C : Set ↥Y} (h : IsIrreducible C) : orderAlong I C = orderAt I h.genericPoint := by
  unfold orderAlong
  exact dif_pos h

/- English proof (authored)
The singleton closures of the two generic points are the two given closures and hence are equal. Scheme spaces distinguish points by their closures, so the two points coincide. The order along each set is the order at the common point.
-/
theorem orderAlong_eq_of_closure_eq {Y : Scheme.{u}} (I : Y.IdealSheafData) {S : Set ↥Y}
    (hS : IsIrreducible S) {C : Set ↥Y} (hC : IsIrreducible C)
    (hcl : closure S = closure C) : orderAlong I S = orderAlong I C := by
  rw [orderAlong_eq_orderAt_genericPoint I hS, orderAlong_eq_orderAt_genericPoint I hC]
  have e1 : closure ({hS.genericPoint} : Set ↥Y) = closure S := by simp
  have e2 : closure ({hC.genericPoint} : Set ↥Y) = closure C := by simp
  have h1 : closure ({hS.genericPoint} : Set ↥Y) = closure ({hC.genericPoint} : Set ↥Y) := by
    rw [e1, e2, hcl]
  rw [(inseparable_iff_closure_eq.mpr h1).eq]

/- English proof (authored)
The zero ideal sheaf has zero stalk at every point. That stalk is contained in the maximal ideal, so the point belongs to the support.
-/
private theorem mem_support_bot {Y : Scheme.{u}} (x : ↥Y) :
    x ∈ (⊥ : Y.IdealSheafData).support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_bot]
  exact bot_le

/- English proof (authored)
Both stalk ideals lie inside the maximal ideal. The stalk of their sum is the sum of the stalk ideals, which is contained in the maximal ideal as well. This gives membership in the support of the sum.
-/
private theorem mem_support_sup_of_mem {Y : Scheme.{u}} {I J : Y.IdealSheafData} {x : ↥Y}
    (hI : x ∈ I.support) (hJ : x ∈ J.support) : x ∈ (I ⊔ J).support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hI hJ ⊢
  rw [stalkIdeal_sup]
  exact sup_le hI hJ

/- English proof (authored)
Induct on the finite selection. The zero ideal from the empty sum has full support. When one ideal is added, the point belongs to its support by hypothesis and to the support of the smaller sum by induction. It then belongs to the support of their sum.
-/
private theorem mem_support_finsetSup_of_forall_mem {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (x : ↥Y) (S : Finset (Fin L.length)) (hx : ∀ j ∈ S, x ∈ (L.get j).support) :
    x ∈ (S.sup fun j => L.get j).support := by
  revert hx
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.sup_empty]
    exact mem_support_bot x
  · intro a s ha ih hS
    rw [Finset.sup_insert]
    exact mem_support_sup_of_mem (hS a (Finset.mem_insert_self a s))
      (ih fun j hj => hS j (Finset.mem_insert_of_mem hj))

/- English proof (authored)
The intersection ideal is the finite sum of the selected boundary ideals. At the specified point each summand has stalk contained in the maximal ideal, so the sum does as well. This is membership in the intersection support.
-/
theorem mem_support_intersectionIdeal {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (x : ↥Y) (hx : ∀ j ∈ J, x ∈ (L.get j).support) :
    x ∈ (intersectionIdeal L J).support := by
  have he : intersectionIdeal L J = J.sup fun j => L.get j :=
    (intersectionIdeal_eq_iSup L J).trans (Finset.sup_eq_iSup J fun j => L.get j).symm
  rw [he]
  exact mem_support_finsetSup_of_forall_mem L x J hx

/- English proof (authored)
Use the boundary-component property from the geometry hypotheses for the admissible triple. It says that the component lies in the support of exactly the boundary divisors indexed by the selected set.
-/
theorem subset_support_iff_mem_of_mem_intersectionComponents (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) :
    C ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J :=
  hGeom.components_subset_divisor_iff T hT.valid J C hC i

/- English proof (authored)
A closed boundary support contains the generic point exactly when it contains the generic point's entire closure, which is the given component. The component containment criterion identifies this with membership of the divisor index in the chosen set.
-/
theorem genericPoint_mem_support_iff_mem (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) :
    (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ (T.boundary.get i).support ↔ i ∈ J := by
  have hgen : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub := subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC i
  have hcl : IsClosed (↑(T.boundary.get i).support : Set ↥T.scheme) :=
    (T.boundary.get i).support.2
  constructor
  · intro hx
    refine hsub.1 ?_
    have hx' : ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) ⊆
        (↑(T.boundary.get i).support : Set ↥T.scheme) := Set.singleton_subset_iff.2 hx
    have hsubc := hcl.closure_subset_iff.2 hx'
    rwa [hgen] at hsubc
  · intro hi
    have hmem : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈
        closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) :=
      subset_closure rfl
    rw [hgen] at hmem
    exact hsub.2 hi hmem

/- English proof (authored)
The hypothesis places the generic point of the component in the locus of order at least the threshold. Over the characteristic-zero base with smooth structural map this locus is closed. It therefore contains the closure of the generic point, which is the component.
-/
theorem subset_orderAtLeastLocus_of_le_orderAlong {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (c : ℕ) (hc : (c : ℕ∞) ≤ orderAlong T.ideal C) :
    C ⊆ orderAtLeastLocus T.ideal c := by
  have : CharZero T.base := hT.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have hmem : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ orderAtLeastLocus T.ideal c := by
    rw [mem_orderAtLeastLocus_iff, ← orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
    exact hc
  have hclosed : IsClosed (orderAtLeastLocus T.ideal c) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal c
  have h2 : closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub :
      closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) ⊆
        orderAtLeastLocus T.ideal c :=
    closure_minimal (Set.singleton_subset_iff.2 hmem) hclosed
  rw [← h2]
  exact hsub

def supportIndices {Y : Scheme.{u}} (L : List Y.IdealSheafData) (x : ↥Y) :
    Finset (Fin L.length) :=
  @Finset.filter _ (fun j => x ∈ (L.get j).support) (Classical.decPred _) Finset.univ

/- English proof (authored)
The index set is obtained by filtering the boundary positions for membership of the given point in the corresponding support. This is exactly the stated condition.
-/
theorem mem_supportIndices {Y : Scheme.{u}} (L : List Y.IdealSheafData) (x : ↥Y)
    (j : Fin L.length) : j ∈ supportIndices L x ↔ x ∈ (L.get j).support := by
  simp [supportIndices]

/- English proof (authored)
Induct on the list. The empty product is the unit ideal of order zero, equal to the empty sum. For a nonempty list, the order of the product of its first factor and the remaining product is the sum of their orders. Use the induction formula for the remaining product.
-/
theorem orderAt_foldr_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (x : ↥X) (L : List X.IdealSheafData) :
    orderAt (L.foldr (· * ·) ⊤) x = (L.map (fun I => orderAt I x)).sum := by
  induction L with
  | nil => simp [orderAt_top]
  | cons I L ih => simp [orderAt_mul k p, ih]

/- English proof (authored)
Restriction to an open preserves order at its points. On the given neighborhood, apply additivity of order to the product expression for the ideal, and use that raising a factor to its exponent multiplies its order by that exponent. A boundary divisor has order one on its support and zero off it. Thus each contribution equals the exponent times the indicator of the divisor support, giving the sum.
-/
theorem orderAt_eq_sum_indicator_support (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (U : T.scheme.Opens)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    (x : ↥T.scheme) (hx : x ∈ U) :
    orderAt T.ideal x =
      ∑ j : Fin T.boundary.length,
        (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.valid.smooth
  have : AlgebraicGeometry.Smooth U.ι := inferInstance
  have : AlgebraicGeometry.Smooth (U.ι ≫ T.structMap) := inferInstance
  have h1 : orderAt (T.ideal.comap U.ι) ⟨x, hx⟩ = orderAt T.ideal x :=
    orderAt_comap T.base T.structMap U.ι T.ideal ⟨x, hx⟩
  have h2 : orderAt (T.ideal.comap U.ι) ⟨x, hx⟩
      = ∑ i : Fin T.boundary.length,
          orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩ := by
    rw [hmon, orderAt_foldr_mul T.base (U.ι ≫ T.structMap) ⟨x, hx⟩]
    simp [List.map_ofFn, List.sum_ofFn]
  have h3 : ∀ i : Fin T.boundary.length,
      orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩
        = (a i : ℕ∞) *
            (↑(T.boundary.get i).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x := by
    intro i
    have hmemlist : T.boundary.get i ∈ T.boundary := by simp
    have hcomap : orderAt ((T.boundary.get i).comap U.ι) ⟨x, hx⟩
        = orderAt (T.boundary.get i) x :=
      orderAt_comap T.base T.structMap U.ι (T.boundary.get i) ⟨x, hx⟩
    rw [orderAt_pow T.base (U.ι ≫ T.structMap) ((T.boundary.get i).comap U.ι) (a i) ⟨x, hx⟩,
      hcomap]
    by_cases hmem : x ∈ (T.boundary.get i).support
    · have hset : x ∈ (↑(T.boundary.get i).support : Set ↥T.scheme) := hmem
      rw [hGeom.orderAt_boundary_eq_one T hT.valid (T.boundary.get i) hmemlist x hmem,
        Set.indicator_of_mem hset]
    · have hset : x ∉ (↑(T.boundary.get i).support : Set ↥T.scheme) := hmem
      rw [(orderAt_eq_zero_iff_not_mem_support (T.boundary.get i) x).2 hmem,
        Set.indicator_apply, if_neg hset]
  calc orderAt T.ideal x = orderAt (T.ideal.comap U.ι) ⟨x, hx⟩ := h1.symm
    _ = ∑ i : Fin T.boundary.length,
          orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩ := h2
    _ = ∑ j : Fin T.boundary.length,
          (a j : ℕ∞) *
            (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x :=
        Finset.sum_congr rfl fun i _ => h3 i

/- English proof (authored)
The indicator of the constant function 1 takes value zero outside the set. The point is outside by hypothesis.
-/
private theorem indicator_one_eq_zero_of_notMem {α : Type u} (s : Set α) (x : α) (h : x ∉ s) :
    s.indicator (fun _ => (1 : ℕ∞)) x = 0 := by
  simp [Set.indicator, h]

/- English proof (authored)
On the set the indicator retains the value of the underlying constant function, which is 1.
-/
private theorem indicator_one_eq_one_of_mem {α : Type u} (s : Set α) (x : α) (h : x ∈ s) :
    s.indicator (fun _ => (1 : ℕ∞)) x = 1 := by
  simp [Set.indicator, h]

/- English proof (authored)
The open neighborhood meets the given component, so it contains the component's generic point. The order along the component is the order at this point. In the local monomial order formula only boundary supports through that point contribute. By the generic-point criterion their indices are exactly the chosen set, and each contributes its exponent. Summing them gives the finite natural-number sum in the statement.
-/
theorem orderAlong_eq_sum_of_monomial (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) {J : Finset (Fin T.boundary.length)}
    {C : Set ↥T.scheme} (hC : C ∈ intersectionComponents T.boundary J) {x : ↥T.scheme} (hxC : x ∈ C)
    (U : T.scheme.Opens) (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤) :
    orderAlong T.ideal C = ((∑ j ∈ J, a j : ℕ) : ℕ∞) := by
  have hgen : closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hξU0 : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ U := by
    by_contra hnot
    have h2 : C ⊆ (↑U : Set ↥T.scheme)ᶜ := by
      rw [← hgen]
      exact closure_minimal (Set.singleton_subset_iff.2 hnot)
        (TopologicalSpace.Opens.isOpen U).isClosed_compl
    exact h2 hxC hxU
  obtain ⟨ξ, hord, hξU, hξs⟩ :
      ∃ ξ : ↥T.scheme, orderAlong T.ideal C = orderAt T.ideal ξ ∧ ξ ∈ U ∧
        ∀ j : Fin T.boundary.length, (ξ ∈ (T.boundary.get j).support ↔ j ∈ J) :=
    ⟨(isIrreducible_of_mem_intersectionComponents hC).genericPoint,
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, hξU0,
      fun j => genericPoint_mem_support_iff_mem hGeom hT hC j⟩
  rw [hord, orderAt_eq_sum_indicator_support hGeom hT U a hmon ξ hξU]
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin T.boundary.length)), j ∉ J →
      (a j : ℕ∞) *
        (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) ξ = 0 := by
    intro j _ hj
    have h1 : ξ ∉ (↑(T.boundary.get j).support : Set ↥T.scheme) := fun hm => hj ((hξs j).1 hm)
    rw [indicator_one_eq_zero_of_notMem _ ξ h1, mul_zero]
  have hone : ∀ j ∈ J,
      (a j : ℕ∞) *
        (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) ξ
        = (a j : ℕ∞) := by
    intro j hj
    have h1 : ξ ∈ (↑(T.boundary.get j).support : Set ↥T.scheme) := (hξs j).2 hj
    rw [indicator_one_eq_one_of_mem _ ξ h1, mul_one]
  rw [← Finset.sum_subset (Finset.subset_univ J) hzero, Finset.sum_congr rfl hone]
  exact (Nat.cast_sum J a).symm

/- English proof (authored)
Apply the local formula expressing the order as a sum weighted by the support indicators. Terms outside the support index set are zero and each term inside it is its exponent. Removing the zero terms gives the claimed sum.
-/
theorem orderAt_eq_sum_supportIndices (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (x : ↥T.scheme) (U : T.scheme.Opens)
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤) :
    orderAt T.ideal x = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) := by
  classical
  have h2 : ∀ j ∈ (Finset.univ : Finset (Fin T.boundary.length)),
      j ∉ supportIndices T.boundary x →
      (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x = 0 := by
    intro j _ hj
    have hx : x ∉ (↑(T.boundary.get j).support : Set ↥T.scheme) := by
      intro hmem
      exact hj ((mem_supportIndices T.boundary x j).2 hmem)
    rw [Set.indicator_apply, if_neg hx, mul_zero]
  have h1 : ∀ j ∈ supportIndices T.boundary x,
      (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x
        = (a j : ℕ∞) := by
    intro j hj
    have hx : x ∈ (↑(T.boundary.get j).support : Set ↥T.scheme) :=
      (mem_supportIndices T.boundary x j).1 hj
    rw [Set.indicator_apply, if_pos hx]
    exact mul_one _
  rw [orderAt_eq_sum_indicator_support hGeom hT U a hmon x hxU, Nat.cast_sum,
    ← Finset.sum_subset (Finset.subset_univ (supportIndices T.boundary x)) h2]
  exact Finset.sum_congr rfl h1

/- English proof (authored)
A candidate meets three requirements, including that its component belongs to the intersection-component family for the selected boundary indices. Apply this condition.
-/
private theorem mem_intersectionComponents_of_isCandidateComponent {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (m : ℕ) (L : List Y.IdealSheafData) (r : ℕ) (J : Finset (Fin L.length)) (C : Set ↥Y)
    (h : IsCandidateComponent I m L r J C) : C ∈ intersectionComponents L J := by
  unfold IsCandidateComponent at h
  simp only [mem_intersectionComponents_iff] at h ⊢
  tauto

/- English proof (authored)
There are finitely many subsets of the finite boundary index set. For each subset its intersection has finitely many components by admissibility and the geometry hypotheses. All candidate pairs lie in the finite union of these pairs of a subset with one of its components. The candidate set is therefore finite.
-/
theorem finite_setOf_isCandidateComponent (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2}.Finite := by
  classical
  have hfin : (⋃ J : Finset (Fin T.boundary.length),
      (fun C : Set ↥T.scheme => ((J, C) : Finset (Fin T.boundary.length) × Set ↥T.scheme)) ''
        intersectionComponents T.boundary J).Finite :=
    Set.finite_iUnion fun J =>
      Set.Finite.image
        (fun C : Set ↥T.scheme => ((J, C) : Finset (Fin T.boundary.length) × Set ↥T.scheme))
        (hGeom.components_finite T hT.valid J)
  refine hfin.subset ?_
  rintro ⟨J, C⟩ ⟨r, hcand⟩
  have hmem : C ∈ intersectionComponents T.boundary J :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary r J C hcand
  exact Set.mem_iUnion.2 ⟨J, Set.mem_image_of_mem _ hmem⟩

/- English proof (authored)
The bound is a natural number and hence is strictly below infinity in the extended natural numbers. Anything at most that bound is also strictly below infinity.
-/
private theorem lt_top_of_le_natCast {a : ℕ∞} {B : ℕ} (h : a ≤ (B : ℕ∞)) : a < ⊤ :=
  h.trans_lt (ENat.natCast_lt_top B)

/- English proof (authored)
The candidate belongs to the intersection-component family, so its order is the order at its generic point. The geometry hypotheses give a finite global order bound for the ideal, which is nonzero on components by admissibility. The order at this point is therefore finite.
-/
theorem orderAlong_lt_top_of_isCandidateComponent (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) {r : ℕ}
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hcand : IsCandidateComponent T.ideal T.mult T.boundary r J C) :
    orderAlong T.ideal C < ⊤ := by
  have hC : C ∈ intersectionComponents T.boundary J := by
    unfold IsCandidateComponent at hcand
    tauto
  obtain ⟨B, hB⟩ :=
    hGeom.orderAt_bounded T hT.valid T.ideal hT.valid.nonzeroOnComponents
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
  exact lt_top_of_le_natCast (hB _)

/- English proof (authored)
The minimum selection size is defined as the infimum of the positive natural numbers for which a set of that cardinality and a candidate component exist. This is the stated infimum.
-/
private theorem minIndexCard_eq_sInf {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    minIndexCard I m L =
      sInf {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C} := rfl

/- English proof (authored)
The set of positive sizes realized by candidates is nonempty by hypothesis. Its infimum in the natural numbers is one of its elements, so it is positive and realized by a candidate. As the infimum, it is at most every other positive size realized by a candidate.
-/
theorem minIndexCard_spec {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData)
    (hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C) :
    1 ≤ minIndexCard I m L ∧
      (∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L (minIndexCard I m L) J C) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C → minIndexCard I m L ≤ r) := by
  classical
  have hne : {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C}.Nonempty := hex
  have hmem : minIndexCard I m L ∈ {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C} := by
    rw [minIndexCard_eq_sInf I m L]
    exact Nat.sInf_mem hne
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨h1, h2, ?_⟩
  intro r hr J C hcand
  rw [minIndexCard_eq_sInf I m L]
  exact Nat.sInf_le ⟨hr, J, C, hcand⟩

/- English proof (authored)
Every size in the defining set is positive. If the set is nonempty, the infimum is an element and is positive. If the set is empty, its natural-number infimum is zero. Thus zero occurs precisely when there is no candidate of positive size.
-/
theorem minIndexCard_eq_zero_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    minIndexCard I m L = 0 ↔
      ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C := by
  rw [minIndexCard_eq_sInf I m L, Nat.sInf_eq_zero]
  constructor
  · rintro (h0 | hempty) hex
    · obtain ⟨h1, -⟩ := h0
      omega
    · obtain ⟨r, hr⟩ := hex
      have h2 : r ∈ (∅ : Set ℕ) := by
        rw [← hempty]
        exact hr
      exact (Set.mem_empty_iff_false r).mp h2
  · intro hne
    refine Or.inr ?_
    ext r
    constructor
    · intro hr
      exact (hne ⟨r, hr⟩).elim
    · intro hr
      exact ((Set.mem_empty_iff_false r).mp hr).elim

/- English proof (authored)
A nonzero minimum means that the set of positive candidate sizes is nonempty. The minimum-size specification gives a selection and component that attain it.
-/
theorem exists_isCandidateComponent_minIndexCard {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (h : minIndexCard I m L ≠ 0) :
    ∃ (J : Finset (Fin L.length)) (C : Set ↥Y), IsCandidateComponent I m L (minIndexCard I m L) J C := by
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C := by
    by_contra hc
    exact h ((minIndexCard_eq_zero_iff I m L).2 hc)
  exact (minIndexCard_spec I m L hex).2.1

/- English proof (authored)
The maximum-order expression is defined as the supremum of the orders of components whose selected indices make them candidates at the minimum size. Indexing the supremum by the selection, component and candidate condition gives the stated formula.
-/
private theorem maxCandidateOrder_eq_iSup_orderAlong {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    maxCandidateOrder I m L =
      ⨆ J : Finset (Fin L.length), ⨆ C : Set ↥Y,
        ⨆ _ : IsCandidateComponent I m L (minIndexCard I m L) J C, orderAlong I C :=
  rfl

/- English proof (authored)
Positive minimum size gives at least one candidate at that size. There are finitely many candidate pairs, so the orders of the pairs at the minimum size attain a maximum. This maximum is the defined supremum since it occurs among the terms and bounds all terms. The attaining component has order at least the mark by candidacy and has finite order by the order bound. These facts give the existence, upper bound and two bounds on the maximum.
-/
theorem maxCandidateOrder_spec (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C ∧
          orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary) ∧
      (∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C →
          orderAlong T.ideal C ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      ((T.mult : ℕ∞) ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      maxCandidateOrder T.ideal T.mult T.boundary < ⊤ := by
  classical
  obtain ⟨J₁, C₁, hcand₁⟩ := exists_isCandidateComponent_minIndexCard T.ideal T.mult T.boundary h
  have hsub : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) p.1 p.2} ⊆
      {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
        ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    exact ⟨minIndexCard T.ideal T.mult T.boundary, hp⟩
  have hfin : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
        p.1 p.2}.Finite :=
    (finite_setOf_isCandidateComponent hGeom hT).subset hsub
  have hne : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
        p.1 p.2}.Nonempty := ⟨(J₁, C₁), hcand₁⟩
  obtain ⟨p₀, hmem₀, hmax₀⟩ :=
    Set.exists_max_image _
      (fun q : Finset (Fin T.boundary.length) × Set ↥T.scheme => orderAlong T.ideal q.2) hfin hne
  have hcand₀ : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      p₀.1 p₀.2 := hmem₀
  have hkey : maxCandidateOrder T.ideal T.mult T.boundary = orderAlong T.ideal p₀.2 := by
    rw [maxCandidateOrder_eq_iSup_orderAlong]
    refine le_antisymm ?_ ?_
    · apply iSup_le
      intro J
      apply iSup_le
      intro C
      apply iSup_le
      intro hc
      exact hmax₀ (J, C) hc
    · exact le_iSup_of_le p₀.1 (le_iSup_of_le p₀.2 (le_iSup_of_le hcand₀ le_rfl))
  refine ⟨⟨p₀.1, p₀.2, hcand₀, hkey.symm⟩, ?_, ?_, ?_⟩
  · intro J C hc
    rw [hkey]
    exact hmax₀ (J, C) hc
  · rw [hkey]
    have hcomp := hcand₀
    unfold IsCandidateComponent at hcomp
    exact hcomp.2.2
  · rw [hkey]
    exact orderAlong_lt_top_of_isCandidateComponent hGeom hT hcand₀

/- English proof (authored)
Take a candidate at the minimum size whose component attains the maximum order. Its chosen index set has the required witness for maximum order.
-/
theorem exists_isMaxOrderIndexSet (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    ∃ J : Finset (Fin T.boundary.length), IsMaxOrderIndexSet T.ideal T.mult T.boundary J := by
  obtain ⟨J, C, hcand, hord⟩ := (maxCandidateOrder_spec hGeom hT h).1
  refine ⟨J, ?_⟩
  unfold IsMaxOrderIndexSet
  exact ⟨C, hcand, hord⟩

/- English proof (authored)
The maximum code is defined as the supremum of the binary codes of selections admitting a component of maximum candidate order. This is the stated set of codes.
-/
private theorem maxBinaryCode_eq_sSup {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    maxBinaryCode I m L =
      sSup {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c} := rfl

/- English proof (authored)
A maximizing selection has a candidate witness at the minimum size. The candidate size condition says that the selection has exactly that cardinality.
-/
private theorem card_eq_minIndexCard_of_isMaxOrderIndexSet {Y : Scheme.{u}} {I : Y.IdealSheafData}
    {m : ℕ} {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J) :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hcand, -⟩ := hJ
  unfold IsCandidateComponent at hcand
  exact hcand.1

/- English proof (authored)
The family of maximum-order selections is nonempty. Their codes form a finite set of natural numbers, so its supremum is attained. The chosen selection attains that code and thus is of maximum order. All maximum-order selections have the same cardinality. If another one had a lexicographically smaller increasing index list, the reversed binary encoding would give it a larger code than the chosen one. This contradicts maximality of the chosen code, proving the stated lexicographic property.
-/
theorem lexMaxIndices_spec (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      ∀ J : Finset (Fin T.boundary.length), IsMaxOrderIndexSet T.ideal T.mult T.boundary J →
        ¬ List.Lex (· < ·) (MonomialCenter.sortedIndices J)
            (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary)) := by
  classical
  obtain ⟨J0, hJ0⟩ := exists_isMaxOrderIndexSet hGeom hT h
  have hbdd : BddAbove {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
    refine Set.Finite.bddAbove (Set.Finite.subset
      (Set.finite_range (fun J : Finset (Fin T.boundary.length) => binaryEncode J)) ?_)
    rintro c ⟨J, -, rfl⟩
    exact Set.mem_range_self J
  have hne : {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c}.Nonempty :=
    ⟨binaryEncode J0, ⟨J0, hJ0, rfl⟩⟩
  have hex : ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧
        binaryEncode J = maxBinaryCode T.ideal T.mult T.boundary := by
    have hmem : maxBinaryCode T.ideal T.mult T.boundary ∈
        {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
          IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
      rw [maxBinaryCode_eq_sSup]
      exact Nat.sSup_mem hne hbdd
    exact hmem
  have hchosen : IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      binaryEncode (lexMaxIndices T.ideal T.mult T.boundary)
        = maxBinaryCode T.ideal T.mult T.boundary := by
    unfold lexMaxIndices
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hchosen.1, ?_⟩
  intro J hJ hlex
  have hcard : J.card = (lexMaxIndices T.ideal T.mult T.boundary).card := by
    rw [card_eq_minIndexCard_of_isMaxOrderIndexSet hJ, card_eq_minIndexCard_of_isMaxOrderIndexSet hchosen.1]
  have hlt : binaryEncode (lexMaxIndices T.ideal T.mult T.boundary) < binaryEncode J :=
    (MonomialCenter.binaryEncode_lt_iff_lex_of_card_eq J (lexMaxIndices T.ideal T.mult T.boundary) hcard).2
      hlex
  have hle : binaryEncode J ≤ binaryEncode (lexMaxIndices T.ideal T.mult T.boundary) := by
    rw [hchosen.2, maxBinaryCode_eq_sSup]
    exact le_csSup hbdd ⟨J, hJ, rfl⟩
  exact absurd hlt (not_lt.2 hle)

/- English proof (authored)
At positive minimum size, the index-selection result says that the chosen selection has maximum order. Every maximum-order selection has minimum candidate size, so the chosen one has that cardinality.
-/
theorem card_lexMaxIndices (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (lexMaxIndices T.ideal T.mult T.boundary).card = minIndexCard T.ideal T.mult T.boundary :=
  card_eq_minIndexCard_of_isMaxOrderIndexSet (lexMaxIndices_spec hGeom hT h).1

/- English proof (authored)
The center definition uses an open part of the intersection only if the minimum size is positive and the requisite preimage is open. When the size is zero its other branch gives the unit ideal.
-/
theorem monomialCenter_eq_top_of_minIndexCard_eq_zero {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (h : minIndexCard I m L = 0) : monomialCenter I m L = ⊤ := by
  unfold monomialCenter
  simp [h]

def centerComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : Set (Set ↥Y) :=
  {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
      orderAlong I C = maxCandidateOrder I m L}

/- English proof (authored)
The center family consists of those components that are candidates at the minimum size for the chosen index set and whose orders attain the maximum. Membership is exactly these two conditions.
-/
theorem mem_centerComponents_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (C : Set ↥Y) :
    C ∈ centerComponents I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
        orderAlong I C = maxCandidateOrder I m L :=
  Iff.rfl

/- English proof (authored)
A member of the center family is a candidate for the chosen index set. The candidate condition places it among the components of the intersection for that set.
-/
theorem centerComponents_subset_intersectionComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    centerComponents I m L ⊆ intersectionComponents L (lexMaxIndices I m L) := by
  intro C hC
  exact mem_intersectionComponents_of_isCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C
    ((mem_centerComponents_iff I m L C).1 hC).1

/- English proof (authored)
The center family consists of components of the chosen intersection. The geometry hypotheses make the preimage of the union of any such family open in that intersection subscheme. Apply this to the center family.
-/
theorem isOpen_preimage_sUnion_centerComponents (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
      ⋃₀ centerComponents T.ideal T.mult T.boundary) :=
  hGeom.sUnion_isOpen T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)

/- English proof (authored)
Both sets are the union over components that are candidates of the minimum size for the chosen indices and have maximum order. A point's membership in either union is witnessed by the same component.
-/
theorem monomialCenterSet_eq_sUnion_centerComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    monomialCenterSet I m L = ⋃₀ centerComponents I m L := by
  ext x
  simp [monomialCenterSet, centerComponents, Set.mem_sUnion]

/- English proof (authored)
Replace the center set by the union of its selected components. The inverse image of this union is open in the chosen intersection subscheme by the component-union result.
-/
theorem isOpen_preimage_monomialCenterSet (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
      monomialCenterSet T.ideal T.mult T.boundary) := by
  rw [monomialCenterSet_eq_sUnion_centerComponents]
  exact isOpen_preimage_sUnion_centerComponents hGeom hT

/- English proof (authored)
Replace the open subset by the equal preimage of the component union. Both ideal constructions are then the kernel of the inclusion of this same open into the intersection subscheme followed by its inclusion into the ambient scheme.
-/
private theorem openSublocusIdeal_eq_componentUnionIdeal {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (𝒞 : Set (Set ↥Y))
    (S : Set ↥(intersectionIdeal L J).subscheme)
    (hEq : S = ⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)
    (hS : IsOpen S) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    openSublocusIdeal (intersectionIdeal L J).subschemeι S hS = componentUnionIdeal L J 𝒞 hop := by
  subst hEq
  rfl

/- English proof (authored)
The minimum size is positive and the preimage of the center set is open. The center therefore uses the branch taking the kernel for this open in the intersection subscheme. The center set is the union of the selected components, so the resulting ideal is the component-union ideal.
-/
theorem monomialCenter_eq_componentUnionIdeal (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    monomialCenter T.ideal T.mult T.boundary =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT) := by
  have hc : minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
        monomialCenterSet T.ideal T.mult T.boundary) :=
    ⟨h, isOpen_preimage_monomialCenterSet hGeom hT⟩
  unfold monomialCenter
  rw [dif_pos hc]
  exact openSublocusIdeal_eq_componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
    (centerComponents T.ideal T.mult T.boundary) _
    (by rw [monomialCenterSet_eq_sUnion_centerComponents]) _ _

/- English proof (authored)
Express the center as the ideal of its selected component union. The support property in the geometry hypotheses identifies the support of that ideal with the union. This union is exactly the center set.
-/
theorem support_monomialCenter (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) =
      monomialCenterSet T.ideal T.mult T.boundary := by
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary,
    monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_support T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

/- English proof (authored)
The chosen index set has a candidate component of maximum order. This component belongs to the center family and is irreducible, hence contains a point. That point belongs to the union defining the center set.
-/
theorem monomialCenterSet_nonempty (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (monomialCenterSet T.ideal T.mult T.boundary).Nonempty := by
  have hbest := (lexMaxIndices_spec hGeom hT h).1
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C, hcand, hord⟩ := hbest
  have hmem : C ∈ centerComponents T.ideal T.mult T.boundary :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).2 ⟨hcand, hord⟩
  have hC : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hC).1
  refine ⟨x, ?_⟩
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  exact Set.mem_sUnion.2 ⟨C, hmem, hx⟩

/- English proof (authored)
The center support is the selected center set, and this set contains a point. The unit ideal has empty support, so the center ideal is proper.
-/
theorem monomialCenter_ne_top (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    monomialCenter T.ideal T.mult T.boundary ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := monomialCenterSet_nonempty hGeom hT h
  have hsupp := support_monomialCenter hGeom hT h
  have hxmem : x ∈ (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := by
    rw [hsupp]
    exact hx
  have hx2 : x ∈ (monomialCenter T.ideal T.mult T.boundary).support := hxmem
  rw [mem_support_iff_stalkIdeal_ne_top, htop, stalkIdeal_top] at hx2
  exact hx2 rfl

/- English proof (authored)
The monomial center ideal is the ideal of a union of components of one boundary intersection. By the smoothness property of such component unions in the geometry hypotheses, its closed subscheme is smooth over the base.
-/
theorem smooth_monomialCenter (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    AlgebraicGeometry.Smooth
      ((monomialCenter T.ideal T.mult T.boundary).subschemeι ≫ T.structMap) := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_smooth T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

/- English proof (authored)
Identify the center ideal with the ideal of the selected component union. The normal-crossings property for these component-union ideals gives strict normal crossings with the given boundary.
-/
theorem hasStrictNormalCrossingsWith_monomialCenter (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    HasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.boundary := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_snc T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

/- English proof (authored)
Take a point of the center support and a selected component containing it. Its order at its generic point is at least the mark by the candidate condition. The locus of points with order at least the mark is closed and contains the generic point, so contains the whole component and the given point.
-/
theorem support_monomialCenter_subset_orderAtLeastLocus (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
      orderAtLeastLocus T.ideal T.mult := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  rintro x ⟨C, hC, hxC⟩
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (lexMaxIndices T.ideal T.mult T.boundary) C :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).1
  have hmem : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  have hord : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hcomp := hcand
    unfold IsCandidateComponent at hcomp
    exact hcomp.2.2
  exact subset_orderAtLeastLocus_of_le_orderAlong hT.valid hmem T.mult hord hxC

/- English proof (authored)
The chosen index set has positive cardinality, so select one of its indices. Each selected component belongs to the corresponding boundary intersection and is contained in the support of this chosen divisor. Every point of the center support lies in such a component and therefore in the union of the boundary supports.
-/
theorem support_monomialCenter_subset_boundary (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
      ⋃ D ∈ T.boundary, (↑D.support : Set ↥T.scheme) := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.1 hx
  have hCcomp : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC
  have hcard : (lexMaxIndices T.ideal T.mult T.boundary).card =
      minIndexCard T.ideal T.mult T.boundary := card_lexMaxIndices hGeom hT h
  have hne : (lexMaxIndices T.ideal T.mult T.boundary).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.pos_of_ne_zero h
  obtain ⟨j, hj⟩ := hne
  have hsub : C ⊆ (↑(T.boundary.get j).support : Set ↥T.scheme) :=
    (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hCcomp j).2 hj
  have hmemlist : T.boundary.get j ∈ T.boundary := by simp
  exact Set.mem_iUnion₂.2 ⟨T.boundary.get j, hmemlist, hsub hxC⟩

/- English proof (authored)
The center has strict normal crossings with the boundary, and its support lies where the original ideal has order at least the mark. The power containment theorem puts the original ideal inside the center ideal raised to that mark. After blowing up the center, the pulled-back center ideal is the exceptional ideal. The controlled transform exists by the blowup factorization theorem for this containment, giving the required product with the exceptional power.
-/
theorem exists_controlledTransform_monomialCenter (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    ∃ J : (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)).IdealSheafData,
      ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult * J =
        T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)) := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.valid.smooth
  have : AlgebraicGeometry.IsNoetherian T.scheme := hT.valid.isNoetherian
  have : AlgebraicGeometry.IsNoetherian (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)) :=
    isNoetherian_of_isBlowupAlongIdealSheaf (Blowup.blowup.isBlowupAlongIdealSheaf_proj (monomialCenter T.ideal T.mult T.boundary))
  have hle : T.ideal ≤ monomialCenter T.ideal T.mult T.boundary ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) T.mult (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
  obtain ⟨J, hJ, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
      (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary) T.ideal T.mult
      (Blowup.blowup.isBlowupAlongIdealSheaf_proj (monomialCenter T.ideal T.mult T.boundary)) hle
  exact ⟨J, hJ⟩

/- English proof (authored)
The preceding center results give a proper ideal, smoothness of its subscheme, strict normal crossings with the boundary and containment of its support in the marked order locus. The controlled-transform theorem supplies an ideal upstairs whose product with the required exceptional power is the total transform. These establish all the specified conditions.
-/
theorem monomialCenter_spec (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    monomialCenter T.ideal T.mult T.boundary ≠ ⊤ ∧
      AlgebraicGeometry.Smooth
        ((monomialCenter T.ideal T.mult T.boundary).subschemeι ≫ T.structMap) ∧
      HasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.boundary ∧
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
        orderAtLeastLocus T.ideal T.mult ∧
      (∃ J : (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)).IdealSheafData,
        ((monomialCenter T.ideal T.mult T.boundary).comap
              (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult * J =
          T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) :=
  ⟨monomialCenter_ne_top hGeom hT h, smooth_monomialCenter hGeom hT h, hasStrictNormalCrossingsWith_monomialCenter hGeom hT h,
    support_monomialCenter_subset_orderAtLeastLocus hGeom hT h,
    exists_controlledTransform_monomialCenter hGeom hT h⟩

/- English proof (authored)
Work in the subspace of the specified set. The singleton of the given point is preirreducible, so it is contained in a maximal preirreducible subset of the subspace. That subset is nonempty and hence irreducible. Its image under the subspace inclusion is irreducible in the ambient scheme and contains the given point. Any larger irreducible subset inside the specified set would give a larger preirreducible subset in the subspace, contradicting maximality. Thus the image is an irreducible component.
-/
theorem exists_isIrreducibleComponentOf_mem {Y : Scheme.{u}} (S : Set ↥Y) (x : ↥Y) (hx : x ∈ S) :
    ∃ C : Set ↥Y, x ∈ C ∧ IsIrreducibleComponentOf C S := by
  have hsing : IsPreirreducible ({(⟨x, hx⟩ : ↥S)} : Set ↥S) := by
    intro u v _ _ hu hv
    obtain ⟨p, hp, hpu⟩ := hu
    obtain ⟨q, hq, hqv⟩ := hv
    rw [Set.mem_singleton_iff] at hp hq
    subst hp
    subst hq
    exact ⟨(⟨x, hx⟩ : ↥S), rfl, hpu, hqv⟩
  obtain ⟨t, ht, hts, hmax⟩ := exists_preirreducible ({(⟨x, hx⟩ : ↥S)} : Set ↥S) hsing
  have hxt : (⟨x, hx⟩ : ↥S) ∈ t := hts (Set.mem_singleton_iff.2 rfl)
  have hxim : x ∈ Subtype.val '' t := ⟨(⟨x, hx⟩ : ↥S), hxt, rfl⟩
  have hsubS : Subtype.val '' t ⊆ S := by
    rintro y ⟨p, -, rfl⟩
    exact p.2
  have hpre : IsPreirreducible (Subtype.val '' t) := by
    intro u v hu hv hu' hv'
    obtain ⟨p, hpim, hpu⟩ := hu'
    obtain ⟨q, hqim, hqv⟩ := hv'
    obtain ⟨p', hp't, hp'eq⟩ := hpim
    obtain ⟨q', hq't, hq'eq⟩ := hqim
    have hp'u : p' ∈ Subtype.val ⁻¹' u := by
      rw [Set.mem_preimage, hp'eq]
      exact hpu
    have hq'v : q' ∈ Subtype.val ⁻¹' v := by
      rw [Set.mem_preimage, hq'eq]
      exact hqv
    obtain ⟨r, hrt, hru, hrv⟩ :=
      ht (Subtype.val ⁻¹' u) (Subtype.val ⁻¹' v) (hu.preimage continuous_subtype_val)
        (hv.preimage continuous_subtype_val) ⟨p', hp't, hp'u⟩ ⟨q', hq't, hq'v⟩
    exact ⟨(r : ↥Y), ⟨r, hrt, rfl⟩, hru, hrv⟩
  have hirr : IsIrreducible (Subtype.val '' t) := ⟨⟨x, hxim⟩, hpre⟩
  have hmaxi : ∀ C' : Set ↥Y, IsIrreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S →
      C' = Subtype.val '' t := by
    intro C' hC' hle hC'S
    have hpre' : IsPreirreducible (Subtype.val ⁻¹' C' : Set ↥S) := by
      intro u v hu hv hu' hv'
      obtain ⟨u₀, hu₀, hu₀e⟩ : ∃ u₀ : Set ↥Y, IsOpen u₀ ∧ Subtype.val ⁻¹' u₀ = u :=
        isOpen_induced_iff.1 hu
      obtain ⟨v₀, hv₀, hv₀e⟩ : ∃ v₀ : Set ↥Y, IsOpen v₀ ∧ Subtype.val ⁻¹' v₀ = v :=
        isOpen_induced_iff.1 hv
      subst hu₀e
      subst hv₀e
      obtain ⟨p, hp, hpu⟩ := hu'
      obtain ⟨q, hq, hqv⟩ := hv'
      obtain ⟨y, hyC', hyu, hyv⟩ :=
        hC'.2 u₀ v₀ hu₀ hv₀ ⟨(p : ↥Y), hp, hpu⟩ ⟨(q : ↥Y), hq, hqv⟩
      exact ⟨(⟨y, hC'S hyC'⟩ : ↥S), hyC', hyu, hyv⟩
    have hsubt : t ⊆ Subtype.val ⁻¹' C' := fun p hp => hle ⟨p, hp, rfl⟩
    have hkey : Subtype.val ⁻¹' C' = t := hmax _ hpre' hsubt
    refine Set.Subset.antisymm ?_ hle
    intro y hy
    refine ⟨(⟨y, hC'S hy⟩ : ↥S), ?_, rfl⟩
    rw [← hkey]
    exact hy
  refine ⟨Subtype.val '' t, hxim, ?_⟩
  show IsIrreducible (Subtype.val '' t) ∧ Subtype.val '' t ⊆ S ∧
    ∀ C' : Set ↥Y, IsIrreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S → C' = Subtype.val '' t
  exact ⟨hirr, hsubS, hmaxi⟩

/- English proof (authored)
Apply the existence of a component through a point to the support of the intersection ideal. Being an irreducible component of this support is the membership condition for the intersection-component family.
-/
theorem exists_mem_intersectionComponents_of_mem_support {Y : Scheme.{u}}
    (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (x : ↥Y)
    (hx : x ∈ (↑(intersectionIdeal L J).support : Set ↥Y)) :
    ∃ C : Set ↥Y, x ∈ C ∧ C ∈ intersectionComponents L J := by
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem (↑(intersectionIdeal L J).support : Set ↥Y) x hx
  exact ⟨C, hxC, (mem_intersectionComponents_iff L J C).2 hcomp⟩

/- English proof (authored)
Suppose a point belongs to the marked order locus. Take a local monomial expression there. The order is the sum of the exponents for the boundary divisors through the point. The mark is positive, so this set of indices is nonempty. The point belongs to the support of their intersection, and a component of that support contains it. The generic order along this component is the sum of the same exponents by the component order formula. It is at least the mark, so the index set and component give a candidate of positive size. This contradicts the zero minimum size.
-/
theorem orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary = 0) :
    orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨U, hxU, a, hmon⟩ := hT.monomialNear x hx
  have hmult : 1 ≤ T.mult := hT.valid.one_le_mult
  have hmle : (T.mult : ℕ∞) ≤ orderAt T.ideal x := (mem_orderAtLeastLocus_iff _ _ _).1 hx
  have hord : orderAt T.ideal x
      = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) :=
    orderAt_eq_sum_supportIndices hGeom hT x U hxU a hmon
  have hJne : (supportIndices T.boundary x).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (supportIndices T.boundary x) with he | hne'
    · exfalso
      rw [he, Finset.sum_empty] at hord
      rw [hord] at hmle
      have hm0 : T.mult ≤ 0 := by exact_mod_cast hmle
      omega
    · exact hne'
  have hxsupp : x ∈ (↑(intersectionIdeal T.boundary (supportIndices T.boundary x)).support :
      Set ↥T.scheme) :=
    mem_support_intersectionIdeal T.boundary (supportIndices T.boundary x) x
      fun j hj => (mem_supportIndices T.boundary x j).1 hj
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem
      (↑(intersectionIdeal T.boundary (supportIndices T.boundary x)).support : Set ↥T.scheme) x hxsupp
  have hCmem : C ∈ intersectionComponents T.boundary (supportIndices T.boundary x) :=
    (mem_intersectionComponents_iff T.boundary (supportIndices T.boundary x) C).2 hcomp
  have hordC : orderAlong T.ideal C
      = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hCmem hxC U hxU a hmon
  have hordm : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [hordC, ← hord]
    exact hmle
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (supportIndices T.boundary x).card (supportIndices T.boundary x) C := by
    unfold IsCandidateComponent
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · assumption
    · assumption
  have hcontr : ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C := (minIndexCard_eq_zero_iff _ _ _).1 h
  have hcard : 1 ≤ (supportIndices T.boundary x).card := by
    have hpos := Finset.card_pos.2 hJne
    omega
  exact hcontr ⟨(supportIndices T.boundary x).card, hcard,
    supportIndices T.boundary x, C, hcand⟩

/- English proof (authored)
If a positive-size candidate existed, its component would have order at least the mark at its generic point. The whole component would then lie in the closed marked order locus. An irreducible component is nonempty, contrary to emptiness of this locus. Thus no positive-size candidate exists and the minimum is zero.
-/
theorem minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (h : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    minIndexCard T.ideal T.mult T.boundary = 0 := by
  rw [minIndexCard_eq_zero_iff]
  rintro ⟨r, hr, J, C, hcand⟩
  have hC : C ∈ intersectionComponents T.boundary J :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary r J C hcand
  have hord : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    unfold IsCandidateComponent at hcand
    exact hcand.2.2
  have hsub : C ⊆ orderAtLeastLocus T.ideal T.mult :=
    subset_orderAtLeastLocus_of_le_orderAlong hT hC T.mult hord
  obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hC).1
  rw [h] at hsub
  exact (Set.mem_empty_iff_false x).mp (hsub hx)

def maxOrderCandidatePairs {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : Set (Finset (Fin L.length) × Set ↥Y) :=
  {p : Finset (Fin L.length) × Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L}

/- English proof (authored)
The family is defined by the condition that the pair is a candidate at the minimum size and that its component order equals the maximum. This is exactly the right-hand condition.
-/
theorem mem_maxOrderCandidatePairs_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (p : Finset (Fin L.length) × Set ↥Y) :
    p ∈ maxOrderCandidatePairs I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L :=
  Iff.rfl

/- English proof (authored)
A maximum-order pair is still one of the candidate pairs, witnessed by the minimum size. All candidate pairs form a finite set, so the subset of maximum-order pairs is finite.
-/
theorem finite_maxOrderCandidatePairs (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    (maxOrderCandidatePairs T.ideal T.mult T.boundary).Finite := by
  refine (finite_setOf_isCandidateComponent hGeom hT).subset ?_
  rintro ⟨J, C⟩ ⟨hcand, -⟩
  exact ⟨minIndexCard T.ideal T.mult T.boundary, hcand⟩

end FunctorialResolution.EmbeddedResolution

end
