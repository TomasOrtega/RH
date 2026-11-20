import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialFactorTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.PrincipalizationCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

/- English proof (authored)
Pullback along the identity leaves each ideal unchanged. The empty list is fixed, and the head and tail of each nonempty list are fixed by this fact and induction, respectively.
-/
theorem list_map_comap_id (B : Scheme.{u}) (E : List B.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap (𝟙 B)) E = E := by
  have h : ∀ D : B.IdealSheafData, D.comap (𝟙 B) = D := fun D => by simp
  induction E with
  | nil => rfl
  | cons D E ih => rw [List.map_cons, h D, ih]

/- English proof (authored)
Substitute the equality of schemes. The comparison morphism is the identity, which fixes the ideal by pullback and fixes its locus by inverse image.
-/
theorem orderAtLeastLocus_comap_eqToHom {A B : Scheme.{u}} (h : A = B) (J : B.IdealSheafData) (c : ℕ) :
    orderAtLeastLocus (J.comap (eqToHom h)) c = (eqToHom h).base ⁻¹' orderAtLeastLocus J c := by
  subst h
  simp

/- English proof (authored)
Substitute the equalities of the structure map, ideal, marking, and boundary. The target carries exactly the admissibility conditions of the given object.
-/
theorem isAdmissible_congr {k : Type u} [Field k] {A : Scheme.{u}}
    {p q : A ⟶ Spec (CommRingCat.of k)} {I J : A.IdealSheafData} {m n : ℕ}
    {E F : List A.IdealSheafData} (hp : p = q) (hI : I = J) (hm : m = n) (hE : E = F)
    (h : (MarkedIdealWithBoundary.mk k A p I m E).IsAdmissible) :
    (MarkedIdealWithBoundary.mk k A q J n F).IsAdmissible := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

/- English proof (authored)
At stage zero both boundaries are the original entries pulled back along the initial isomorphism. At each actual step both descriptions take strict transforms of the same previous entries and append the same exceptional ideal. Induction through the sequence length gives the equality.
-/
theorem ofMarkedSequence_boundary_eq_of_le {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) (hi : i ≤ s.length) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.boundary_zero]
      exact s.boundary_zero.symm
  | succ i ih =>
      intro hi
      have hlt : i < s.length := hi
      rw [BlowupSequenceData.boundary_succ, ih (Nat.le_of_lt hlt)]
      exact (s.boundary_succ i hlt).symm

end

section

abbrev principalizationOfDimLe (T : MarkedIdealWithBoundary.{u}) (A : PrincipalizationAssignment.{u}) :
    (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups :=
  fun S _ => A S

/- English proof (authored)
An inverse image of an affine open is an open subset of the Noetherian source. Every such subset is quasi-compact, so the morphism is quasi-compact.
-/
private theorem quasiCompact_of_isNoetherian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : AlgebraicGeometry.IsNoetherian X) : AlgebraicGeometry.QuasiCompact f := by
  have := h
  infer_instance

/- English proof (authored)
A smooth morphism is locally of finite presentation and therefore locally of finite type.
-/
private theorem locallyOfFiniteType_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : AlgebraicGeometry.Smooth f) : AlgebraicGeometry.LocallyOfFiniteType f := by
  have := h
  infer_instance

/- English proof (authored)
The conversion to a marked sequence preserves its length, so the final stage is within range. The marked transform results give a smooth structure map, nonvanishing of the final ideal on components, strict normal crossing position of the boundary, and a Noetherian final scheme. Smoothness gives local finite type and the Noetherian source gives quasi-compactness. The characteristic and positive marking remain those of the original admissible object, proving all the conditions.
-/
theorem isAdmissible_tripleAtLength (_hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := by
  have hlen : s.length ≤ s.toMarkedSequenceOfBlowups.length :=
    le_of_eq (MarkedBlowupSequenceData.toMarkedSequence_length s).symm
  have hsm : Smooth (s.proj s.length ≫ T.structMap) := by
    have h := MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec] at h
  have hnz : NonzeroOnComponents (s.ideal s.length) := by
    have h := MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hT
      s.toMarkedSequenceOfBlowups s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_ideal] at h
  have hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ T.structMap) (s.boundary s.length) := by
    have h := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_boundary] at h
  have hno : AlgebraicGeometry.IsNoetherian (s.obj s.length) := by
    have h := MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at h
  exact ⟨hT.charZero, locallyOfFiniteType_of_smooth _ hsm, hnz, hT.one_le_mult,
    quasiCompact_of_isNoetherian _ hno, hsm, hsnc⟩

/- English proof (authored)
The object with the new ideal and marking uses the final stage scheme. The geometric dimension comparison bounds the dimension of that stage by the original dimension. Passing from the data to the marked sequence preserves the scheme and length, so the same bound applies to this object.
-/
theorem tripleAtLength_dim_le (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc := by
  rw [tripleAtLength_dim]
  have hlen : s.length ≤ s.toMarkedSequenceOfBlowups.length :=
    le_of_eq (MarkedBlowupSequenceData.toMarkedSequence_length s).symm
  have h := hG.monomialInputs.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length hlen
  rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at h

/- English proof (authored)
The last original marked object is admissible. Its chosen monomial and nonmonomial parts therefore form a splitting by existence of a splitting on admissible objects. These two parts are exactly the factors in the claim.
-/
theorem isMonomialSplitting_lastNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) := by
  have h := hG.isMonomialSplitting_monomialPart_nonMonomialPart (tripleAtLength T s (s.ideal s.length) T.mult)
    (isAdmissible_tripleAtLength hG hT s)
  exact h

/- English proof (authored)
The final ideal is nonzero on components by admissibility of the final marked object. The nonmonomial factor in its splitting is then nonzero on components as well. Apply the geometric bounded-order theorem on that final scheme to obtain a finite uniform bound.
-/
theorem exists_orderAt_lastNonMonomialPart_le (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    ∃ B : ℕ, ∀ x : ↥(s.obj s.length), orderAt (lastNonMonomialPart T s) x ≤ (B : ℕ∞) := by
  have hv := isAdmissible_tripleAtLength hG hT s
  have hnz : NonzeroOnComponents (s.ideal s.length) := hv.nonzeroOnComponents
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hnz' : NonzeroOnComponents (lastNonMonomialPart T s) :=
    hsplit.nonzeroOnComponents_nonMonomial hnz
  exact hG.monomialInputs.orderAt_bounded (tripleAtLength T s (s.ideal s.length) T.mult) hv
    (lastNonMonomialPart T s) hnz'

/- English proof (authored)
Choose a finite uniform bound for the order of the last nonmonomial factor. The order at each point is then bounded by its maximum, defined as the supremum of the witnessed natural-number orders. This is the desired maximum.
-/
theorem orderAt_lastNonMonomialPart_le_maxOrderNonMonomial (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (x : ↥(s.obj s.length)) :
    orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞) := by
  obtain ⟨B, hB⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
  have h : maxOrderNonMonomial T s = maxOrder (lastNonMonomialPart T s) := rfl
  rw [h]
  exact orderAt_le_maxOrder (lastNonMonomialPart T s) hB x

abbrev nonMonomialTriple (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : MarkedIdealWithBoundary.{u} :=
  tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)

/- English proof (authored)
Use admissibility of the final original marked object for the scheme, structure map, and boundary. Its nonmonomial factor is nonzero on components by the splitting and the nonvanishing of the original final ideal. The continuation condition puts the new marking at least as high as the original positive one. Thus replacing the ideal and marking gives an admissible object.
-/
theorem isAdmissible_nonMonomialTriple (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s) :
    (nonMonomialTriple T s).IsAdmissible := by
  have hbase : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit : IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) :=
    isMonomialSplitting_lastNonMonomialPart hG hT s
  have hnz0 : NonzeroOnComponents (s.ideal s.length) := hbase.nonzeroOnComponents
  have hnz : NonzeroOnComponents (lastNonMonomialPart T s) :=
    hsplit.nonzeroOnComponents_nonMonomial hnz0
  have hmult : 1 ≤ maxOrderNonMonomial T s :=
    le_trans hT.one_le_mult ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  exact ⟨hbase.charZero, hbase.locallyOfFiniteType, hnz, hmult, hbase.quasiCompact, hbase.smooth,
    hbase.snc⟩

end

section

/- English proof (authored)
The nonmonomial triple is admissible, its dimension is within the assignment bound, and its order is bounded by its own marking, the maximum nonmonomial order. Thus the assignment supplies the order bounds along its sequence. The continuation condition makes that marking at least the original marking. Apply the theorem on reusing a sequence for the nonmonomial factor as a marked sequence for the entire split ideal, using the admissibility and splitting of the original final object.
-/
theorem isMarked_seqAtEnd_lastNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (MarkedBlowupSequenceData.ofMarkedSequence
          (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
            (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) := by
  have hμ : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hadmLast : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hsplit : IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) :=
    isMonomialSplitting_lastNonMonomialPart hG hT s
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hord := hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  exact isMarked_sequenceData_of_orderAt_le hG hadmLast hsplit hμ
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) hord

def continuationByNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
      (s.boundary s.length) :=
  BlowupSequenceData.toMarkedBlowupSequenceData
    (MarkedBlowupSequenceData.ofMarkedSequence
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData
    (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)
    (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)

@[simp]
/- English proof (authored)
The continuation uses the underlying blowup data of the assigned nonmonomial sequence and changes its marking. The underlying data retain the original number of steps.
-/
theorem continuationByNonMonomialPart_length (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).length =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s _ _)).length := by
  exact MarkedBlowupSequenceData.ofMarkedSequence_length
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s _ _))

/- English proof (authored)
Take a point of the original order locus and map it by the inverse isomorphism. Pullback along this inverse of the already transported ideal recovers the original ideal. By smooth invariance under the inverse morphism, the image point lies in the order locus of the transported ideal. It witnesses nonemptiness.
-/
private theorem orderAtLeastLocus_comap_iso_nonempty {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    (hp : AlgebraicGeometry.Smooth p) (e : Y ≅ X) (N : X.IdealSheafData) (c : ℕ)
    (hne : (orderAtLeastLocus N c).Nonempty) :
    (orderAtLeastLocus (N.comap e.hom) c).Nonempty := by
  have := hp
  have : AlgebraicGeometry.Smooth e.inv := inferInstance
  obtain ⟨x, hx⟩ := hne
  have hcomp : (N.comap e.hom).comap e.inv = N := by
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id]
    simp
  have hsub := image_orderAtLeastLocus_comap_subset k p e.inv (N.comap e.hom) c
  rw [hcomp] at hsub
  exact ⟨_, hsub (Set.mem_image_of_mem _ hx)⟩

/- English proof (authored)
The assignment resolves the admissible nonmonomial triple because the dimension and order bounds hold. If its sequence had length zero, resolution would make the order locus of its initial ideal empty at stage zero. But the continuation condition gives a point of the original nonmonomial order locus at its maximum marking. Transport through the initial isomorphism preserves nonemptiness, a contradiction. The length is therefore positive.
-/
theorem seqAtEnd_lastNonMonomialPart_length_pos (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    0 < (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s _ _)).length := by
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have key : 0 < (A (nonMonomialTriple T s)).length := by
    by_contra hzero
    have hlen : (A (nonMonomialTriple T s)).length = 0 := by omega
    have hres := hspec.resolves (nonMonomialTriple T s) hadmNonMonomial hdim' hob
    rw [MarkedSequenceOfBlowups.isResolution_iff] at hres
    rw [MarkedSequenceOfBlowups.lastIdeal_eq] at hres
    rw [hlen] at hres
    rw [MarkedSequenceOfBlowups.ideal_zero] at hres
    have := hadmNonMonomial.charZero
    have hsm0 : AlgebraicGeometry.Smooth ((A (nonMonomialTriple T s)).projectionToSpec 0) :=
      MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hadmNonMonomial
        (A (nonMonomialTriple T s)) 0 (Nat.zero_le _)
    have hne : (orderAtLeastLocus ((nonMonomialTriple T s).ideal.comap
        (A (nonMonomialTriple T s)).isoZero.hom) (nonMonomialTriple T s).mult).Nonempty :=
      orderAtLeastLocus_comap_iso_nonempty ((A (nonMonomialTriple T s)).projectionToSpec 0) hsm0
        (A (nonMonomialTriple T s)).isoZero (nonMonomialTriple T s).ideal
        (nonMonomialTriple T s).mult (((nonMonomialOrderReductionContinues_iff T s).1 hcont).2)
    exact absurd hres (Set.nonempty_iff_ne_empty.mp hne)
  exact key

/- English proof (authored)
The final dimension bound permits the recursive call with the last nonmonomial factor and its maximum marking. The resulting data meet the markedness test for the original final ideal and marking. The recursive rule therefore appends those data with the original marking, which is the stated continuation.
-/
theorem extendByNonMonomialPart_eq_append (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s) :
    extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s =
      s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv := by
  have h := appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
    (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))
    (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)
  exact h

private def maxOrderNonMonomialPart {k : Type u} [Field k] (D : MarkedSchemeWithCenter.{u} k) : ℕ :=
  maxOrder (nonMonomialPart D.boundary D.ideal)

/- English proof (authored)
After substituting the equality of ambient schemes, transport is along the identity isomorphism. It fixes the ideal and boundary, so it fixes the nonmonomial factor and its maximum order.
-/
private theorem nonMonomialOrder_transport_eqToIso {k : Type u} [Field k] (D : MarkedSchemeWithCenter.{u} k)
    {Y : Scheme.{u}} (hY : Y = D.ambient) :
    maxOrderNonMonomialPart (D.transport (eqToIso hY)) = maxOrderNonMonomialPart D := by
  subst hY
  rw [eqToIso_refl, MarkedSchemeWithCenter.transport_refl]

/- English proof (authored)
Substitute the equality of boundary lists and the equality of starting ideals. The splitting condition is then exactly the one assumed.
-/
private theorem isMonomialSplitting_of_boundary_eq_of_ideal_eq {X : Scheme.{u}}
    {E F : List X.IdealSheafData} {I J M N : X.IdealSheafData} (hE : E = F) (hI : I = J)
    (h : IsMonomialSplitting F J M N) : IsMonomialSplitting E I M N := by
  subst hE
  subst hI
  exact h

/- English proof (authored)
The two descriptions start with the same pullback along the initial isomorphism. At the next stage the exceptional ideal and blowup map agree, so applying the same residual construction to equal previous transforms gives equal successor transforms. Induction proves equality at every stage.
-/
private theorem controlledTransform_ofMarkedSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (J : X.IdealSheafData) (c : ℕ) (i : ℕ) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.controlledTransform J c i
      = MarkedSequenceOfBlowups.controlledTransform s J c i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      exact congrArg
        (fun Z : (s.schemeAt i).IdealSheafData =>
          residualByPow (Z.comap (s.transitionMapSucc i)) (s.exceptionalDivisor i) c) ih

/- English proof (authored)
The continuation length equals that of the assigned nonmonomial sequence. The latter is positive by resolution and nonemptiness of the starting nonmonomial order locus.
-/
private theorem continuationByNonMonomialPart_length_pos (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    0 < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length := by
  rw [continuationByNonMonomialPart_length hG hspec hT hdim s hcont]
  exact seqAtEnd_lastNonMonomialPart_length_pos hG hspec hT hdim s hcont

/- English proof (authored)
The continuation uses the underlying blowup sequence and the same starting boundary as the assigned nonmonomial sequence. The comparison of boundary recursions identifies their boundaries at the common final index.
-/
private theorem continuationByNonMonomialPart_boundary_length (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).boundary
        (continuationByNonMonomialPart hG hspec hT hdim s hcont).length
      = (A (nonMonomialTriple T s)).boundary (A (nonMonomialTriple T s)).length :=
  ofMarkedSequence_boundary_eq_of_le (A (nonMonomialTriple T s)) (A (nonMonomialTriple T s)).length le_rfl

/- English proof (authored)
The continuation records the controlled transforms of the original final ideal with its original marking on the assigned nonmonomial blowup sequence. The comparison between controlled transforms on the sequence and its underlying data therefore gives the displayed identification at the last stage.
-/
private theorem continuationByNonMonomialPart_ideal_length (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal (continuationByNonMonomialPart hG hspec hT hdim s hcont).length
      = MarkedSequenceOfBlowups.controlledTransform (A (nonMonomialTriple T s))
          (tripleAtLength T s (s.ideal s.length) T.mult).ideal
          (tripleAtLength T s (s.ideal s.length) T.mult).mult
          (A (nonMonomialTriple T s)).length :=
  controlledTransform_ofMarkedSequence
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)))
    (s.ideal s.length) T.mult
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).length

/- English proof (authored)
The assigned sequence has order bounds because the nonmonomial triple is admissible and meets the dimension and initial order bounds. The original marking is at most the nonmonomial marking. The splitting theorem along this sequence identifies the transformed original ideal as a product whose nonmonomial factor is the current ideal of the assigned sequence. At the last stage the continuation has that transformed original ideal and the same boundary. Its final marked object is admissible, so uniqueness of the monomial splitting identifies its chosen nonmonomial factor with the final ideal of the assigned sequence.
-/
private theorem nonMonomialPart_continuationByNonMonomialPart_length (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    nonMonomialPart
        ((continuationByNonMonomialPart hG hspec hT hdim s hcont).boundary
          (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)
        ((continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal
          (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)
      = (A (nonMonomialTriple T s)).ideal (A (nonMonomialTriple T s)).length := by
  have hmu : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hadmLast : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hsplit : IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) :=
    isMonomialSplitting_lastNonMonomialPart hG hT s
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hordA := hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  have hsp := (isMonomialSplitting_controlledTransform_monomialFactor hG hadmLast hsplit hmu (A (nonMonomialTriple T s)) hordA
      (A (nonMonomialTriple T s)).length le_rfl).1
  have hvalid := isAdmissible_tripleAtLength hG hadmLast (continuationByNonMonomialPart hG hspec hT hdim s hcont)
  exact hG.nonMonomialPart_eq_of_isMonomialSplitting _ hvalid _ _
    (isMonomialSplitting_of_boundary_eq_of_ideal_eq (continuationByNonMonomialPart_boundary_length hG hspec hT hdim s hcont)
      (continuationByNonMonomialPart_ideal_length hG hspec hT hdim s hcont) hsp)

/- English proof (authored)
The current maximum marking is positive. The assignment resolves the nonmonomial triple since it is admissible and meets the dimension and order bounds, so its final locus at this marking is empty. Its specification also bounds order along the sequence. Apply the maximum-order estimate for an empty locus at a positive threshold to obtain the strict inequality.
-/
private theorem maxOrder_idealAtLength_lt_maxOrderNonMonomial (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    maxOrder ((A (nonMonomialTriple T s)).ideal (A (nonMonomialTriple T s)).length)
      < maxOrderNonMonomial T s := by
  have hmu : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hmu1 : 1 ≤ maxOrderNonMonomial T s := le_trans hT.one_le_mult hmu
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hres := hspec.resolves (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hres
  exact maxOrder_ideal_length_lt_of_orderAtLeastLocus_eq_empty (A (nonMonomialTriple T s))
    (hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob) hres hmu1

/- English proof (authored)
The extension appends a continuation of positive length. Its final data are the final continuation data under the stage identification, which preserves the maximum nonmonomial order. The continuation's final nonmonomial factor equals the last ideal of the assigned nonmonomial sequence by the transformed splitting. Resolution of that sequence makes its maximum strictly smaller than the previous maximum. These identities transfer the decrease to the extension.
-/
theorem maxOrderNonMonomial_extendByNonMonomialPart_lt (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s) :
    maxOrderNonMonomial T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s) < maxOrderNonMonomial T s := by
  have ht : 0 < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length :=
    continuationByNonMonomialPart_length_pos hG hspec hT hdim s hcont
  have hconv : maxOrderNonMonomial T (s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv)
      = maxOrder (nonMonomialPart
          ((continuationByNonMonomialPart hG hspec hT hdim s hcont).boundary
            (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)
          ((continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal
            (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)) := by
    show maxOrderNonMonomialPart ((s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv).dataAt
      (s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv).length) = _
    rw [MarkedBlowupSequenceData.append_dataAt_last s (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv ht]
    exact nonMonomialOrder_transport_eqToIso _ _
  rw [extendByNonMonomialPart_eq_append hG hinv hspec hT hdim s hcont, hconv,
    nonMonomialPart_continuationByNonMonomialPart_length hG hspec hT hdim s hcont]
  exact maxOrder_idealAtLength_lt_maxOrderNonMonomial hG hspec hT hdim s hcont

end

section

/- English proof (authored)
The empty data end at stage zero with the starting ideal and boundary. Their final nonmonomial factor is therefore the original nonmonomial factor, and their maxima are equal.
-/
private theorem maxOrderNonMonomial_emptyMarkedBlowupSequenceData (T : MarkedIdealWithBoundary.{u}) :
    maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) =
      maxOrder (nonMonomialPart T.boundary T.ideal) := by
  rfl

/- English proof (authored)
At index zero the maximum is the starting maximum. At each successor in range the previous iterate continues, so the extension strictly decreases its natural-number maximum. By induction the previous maximum plus its index is bounded by the initial maximum. The decrease by at least one offsets the increment of the index, giving the bound at the successor.
-/
private theorem maxOrderNonMonomial_iter_add_le_of_forall_le (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (N : ℕ)
    (hall : ∀ f : ℕ, f ≤ N → NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)) (f : ℕ) :
    f ≤ N →
      maxOrderNonMonomial T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) + f ≤
        maxOrder (nonMonomialPart T.boundary T.ideal) := by
  induction f with
  | zero =>
      intro _
      have h0 : maxOrderNonMonomial T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) 0) =
          maxOrder (nonMonomialPart T.boundary T.ideal) := by
        rw [nonMonomialOrderReductionIter_zero hinv T (principalizationOfDimLe T A)]
        exact maxOrderNonMonomial_emptyMarkedBlowupSequenceData T
      omega
  | succ f ih =>
      intro hf
      have hf' : f ≤ N := by omega
      have hc := hall f hf'
      have hstep := nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) f hc
      have hlt := maxOrderNonMonomial_extendByNonMonomialPart_lt hG hinv hspec hT hdim
        (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc
      have hih := ih hf'
      rw [hstep]
      omega

/- English proof (authored)
If the final iterate continued, every earlier iterate would have continued as well, since any stopped iterate stays fixed forever. The maximum-decrease bound would then give that the final maximum plus the iteration count is at most the starting maximum. The iteration count is already one greater than the starting maximum, which is impossible.
-/
theorem not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) :
    ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) := by
  intro hcont
  rw [nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)] at hcont
  have hall : ∀ f : ℕ, f ≤ maxOrder (nonMonomialPart T.boundary T.ideal) + 1 →
      NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) := by
    intro f hf
    by_contra hnc
    have he := nonMonomialOrderReductionIter_eq_of_not_continues hinv T (principalizationOfDimLe T A) f hnc
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) hf
    rw [he] at hcont
    exact hnc hcont
  have hfin := maxOrderNonMonomial_iter_add_le_of_forall_le hG hinv hspec hT hdim
    (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) hall
    (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) le_rfl
  omega

/- English proof (authored)
At one more than the original maximum, the iterate is by definition the completed reduction and its continuation condition fails. All subsequent iterates are equal to this stopped iterate. Apply this stability at the given later index.
-/
theorem nonMonomialOrderReductionIter_eq_of_maxOrder_lt (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (g : ℕ)
    (hg : maxOrder (nonMonomialPart T.boundary T.ideal) + 1 ≤ g) :
    nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) g = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
  have hnc : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)) := by
    rw [← nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)]
    exact not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  rw [nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)]
  exact nonMonomialOrderReductionIter_eq_of_not_continues hinv T (principalizationOfDimLe T A)
    (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) hnc g hg

/- English proof (authored)
The data at i have the given center and its support is nonempty. Their boundary support is the marked sequence's boundary locus, so the given certificate is exactly the certificate required for those data.
-/
private theorem hasPrincipalizationCenter_of_principalizationCertificate {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (t : MarkedBlowupSequenceData p I m E) (μ i : ℕ)
    (hne : (↑(t.center i).support : Set ↥(t.obj i)).Nonempty)
    (hcert : PrincipalizationCertificate (t.obj i) (t.proj i ≫ p) (t.ideal i) μ
      (t.toMarkedSequenceOfBlowups.boundaryLocus i) (t.center i)) :
    HasPrincipalizationCenter μ (t.dataAt i) := by
  refine ⟨hne, ?_⟩
  rw [MarkedBlowupSequenceData.boundarySupport_dataAt]
  exact hcert

/- English proof (authored)
The nonmonomial triple meets the assignment's admissibility, dimension, and order bounds. Its assigned sequence therefore has nonempty centers and certificates, and its stage orders satisfy the required bound. The certificate comparison for a monomial splitting transfers each certificate to the original controlled transform with the original marking. The continuation has that transformed ideal, the same center and projection, and the same boundary. The last equality follows from the common boundary recursion, so their boundary loci also agree. Together with nonemptiness of the center, the transferred certificate gives the asserted stage property.
-/
private theorem hasCenter_continuationByNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) (i : ℕ)
    (hi : i < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length) :
    HasPrincipalizationCenter T.mult ((continuationByNonMonomialPart hG hspec hT hdim s hcont).dataAt i) := by
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hmu : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hadmLast : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hord := hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  have hcertA := hspec.cert (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  have hne := hspec.center_nonempty (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  rw [continuationByNonMonomialPart_length hG hspec hT hdim s hcont] at hi
  have hprinc := principalizationCertificate_controlledTransform hG hadmLast hsplit hmu
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) hord hcertA i hi
  have hidl : (continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal i =
      MarkedSequenceOfBlowups.controlledTransform
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)))
        (s.ideal s.length) T.mult i :=
    controlledTransform_ofMarkedSequence
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)))
      (s.ideal s.length) T.mult i
  have hproj : (continuationByNonMonomialPart hG hspec hT hdim s hcont).proj i =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).projectionToBase i :=
    BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).toSequenceOfBlowups i
  have hbd : (continuationByNonMonomialPart hG hspec hT hdim s hcont).toMarkedSequenceOfBlowups.boundary i =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).boundary i := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary]
    exact ofMarkedSequence_boundary_eq_of_le
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) i (le_of_lt hi)
  have hloc : (continuationByNonMonomialPart hG hspec hT hdim s hcont).toMarkedSequenceOfBlowups.boundaryLocus i =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).boundaryLocus i := by
    apply Set.ext
    intro x
    rw [MarkedSequenceOfBlowups.mem_boundaryLocus_iff
      (continuationByNonMonomialPart hG hspec hT hdim s hcont).toMarkedSequenceOfBlowups i x]
    constructor
    · intro hx
      rw [hbd] at hx
      exact (MarkedSequenceOfBlowups.mem_boundaryLocus_iff
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) i x).2 hx
    · intro hx
      have hx' := (MarkedSequenceOfBlowups.mem_boundaryLocus_iff
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) i x).1 hx
      rw [← hbd] at hx'
      exact hx'
  refine hasPrincipalizationCenter_of_principalizationCertificate (continuationByNonMonomialPart hG hspec hT hdim s hcont) T.mult i (hne i hi) ?_
  rw [hproj, hidl, hloc]
  exact hprinc

/- English proof (authored)
At zero the sequence is empty, so there is no center to check. If an iterate has stopped, the successor is the same sequence and the induction hypothesis applies. Otherwise the successor appends the nonmonomial continuation. The previous stages have the property by induction, and the continuation stages have it by the certificate comparison. Invariance under isomorphism lets the append theorem combine the two.
-/
private theorem hasCenter_nonMonomialOrderReductionIter (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (f : ℕ) :
    ∀ i < (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length,
      HasPrincipalizationCenter T.mult ((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).dataAt i) := by
  induction f with
  | zero =>
      intro i hi
      rw [nonMonomialOrderReductionIter_zero hinv T (principalizationOfDimLe T A)] at hi
      rw [emptyMarkedBlowupSequenceData_length] at hi
      exact absurd hi (Nat.not_lt_zero i)
  | succ f ih =>
      by_cases hc : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)
      · have he : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (f + 1) =
            (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).append
              (continuationByNonMonomialPart hG hspec hT hdim (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc) hinv := by
          rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) f hc,
            extendByNonMonomialPart_eq_append hG hinv hspec hT hdim (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc]
        rw [he]
        intro i hi
        exact MarkedBlowupSequenceData.append_dataAt_of_forall _ _ hinv
          (fun D => HasPrincipalizationCenter T.mult D)
          (isInvariantUnderIso_hasPrincipalizationCenter hG.maxContactTransport T.mult) ih
          (fun j hj => hasCenter_continuationByNonMonomialPart hG hspec hT hdim _ hc j hj) i hi
      · rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) f hc]
        exact ih

/- English proof (authored)
The completed nonmonomial reduction is the iterate at its prescribed stopping bound. The stage property established for every iterate therefore holds for this one.
-/
theorem hasCenter_nonMonomialOrderReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (i : ℕ)
    (hi : i < (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).dataAt i) := by
  rw [nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)] at hi ⊢
  exact hasCenter_nonMonomialOrderReductionIter hG hinv hspec hT hdim _ i hi

/- English proof (authored)
The given point makes the final scheme nonempty. The final nonmonomial order has a finite upper bound, so its maximum is attained and its maximum-order locus is nonempty. Since the reduction has stopped, the other continuation condition must fail, meaning this maximum is strictly below the original marking. The order at the given point is at most that maximum, giving the claimed strict bound.
-/
theorem orderAt_lastNonMonomialPart_nonMonomialOrderReduction_lt (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (x : ↥((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).obj (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length)) :
    orderAt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) x < ((T.mult : ℕ) : ℕ∞) := by
  have hB : ∀ y : ↥((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).obj (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length),
      orderAt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) y ≤
        ((maxOrderNonMonomial T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) : ℕ) : ℕ∞) :=
    fun y => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) y
  have : Nonempty
      ↥((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).obj (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) := ⟨x⟩
  have hne : (orderAtLeastLocus (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))
      (maxOrder (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))))).Nonempty :=
    orderAtLeastLocus_maxOrder_nonempty (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) hB
  have hnc : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) :=
    not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  rw [nonMonomialOrderReductionContinues_iff] at hnc
  have hmax : maxOrderNonMonomial T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) =
      maxOrder (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) := rfl
  have hlt : maxOrder (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) < T.mult := by
    by_contra hle
    push Not at hle
    exact hnc ⟨by rw [hmax]; exact hle, by rw [hmax]; exact hne⟩
  exact orderAt_lt_of_maxOrder_lt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) hB hlt x

end

end FunctorialResolution.EmbeddedResolution

end
