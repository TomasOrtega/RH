import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

/- English proof (authored)
Adding the marked ideal and boundary and passing to the marked sequence preserves the underlying sequence of blowups. Its projection at each stage is therefore the same as the projection in the original data.
-/
private theorem toMarkedSequence_projectionToBase_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (d : BlowupSequenceData X) (h : d.IsMarked p I m E) (n : ℕ) :
    ((d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups).projectionToBase n = d.projectionToBase n :=
  BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n

/- English proof (authored)
At stage zero the embedding is the initial smaller-scheme isomorphism followed by the original closed immersion, and the ambient projection is the identity. This gives the first commuting square. At each successor the two transition maps commute with the embeddings. Compose that square with the preceding projection square and use the successor rule for projections to obtain the next square.
-/
private theorem embeddingIntoAmbientBlowupSequence_comp_projectionToBase {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (d : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < d.length, ∀ W ∈ irreducibleComponents ↥(d.obj i), ¬W ⊆ ↑(d.center i).support)
    (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι d hres hno hcen n ≫ (ambientBlowupSequence ι d hres hno hcen).projectionToBase n =
      d.projectionToBase n ≫ ι := by
  induction n with
  | zero =>
    have hiso : (ambientBlowupSequence ι d hres hno hcen).isoZero.hom = 𝟙 X :=
      congrArg (fun e => Iso.hom e) (ambientBlowupSequence_isoObjZero ι d hres hno hcen)
    rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.projectionToBase_zero, embeddingIntoAmbientBlowupSequence_zero, hiso]
    exact Category.comp_id _
  | succ m ih =>
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_succ, ← Category.assoc,
      embeddingIntoAmbientBlowupSequence_succ_comp_map ι d hres hno hcen m, Category.assoc, ih, ← Category.assoc]

/- English proof (authored)
Apply the ambient projection square to the chosen boundary divisor and the underlying blowup data of its marked sequence. The comparison of marked and underlying data identifies their projections, giving the desired formula.
-/
theorem embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbientBlowupSequence_comp_projectionToBase (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t
  rw [MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase (MarkedBlowupSequenceData.ofMarkedSequence s) t]
  exact h

/- English proof (authored)
The marked ambient projection to the ground field is the projection to the original ambient scheme followed by its structure map. Compose this with the stage embedding and use the projection square to factor through the original divisor. The divisor inclusion followed by the ambient structure map is the original divisor structure map, so the result is the divisor-stage projection to the ground field.
-/
theorem projectionToSpec_eq_comp_ambientMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hB : (pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToBase t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t :=
    toMarkedSequence_projectionToBase_eq _ hmk t
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

/- English proof (authored)
The ambient projection at stage t+1 of the prepended sequence agrees with the unprepended ambient projection at t. After embedding the divisor stage, the projection square identifies the resulting map with the divisor projection followed by the original divisor inclusion. Compose with the ambient structure map. Since this composition gives the divisor's structure map on the original divisor, the full composite is its stage-t projection to the ground field.
-/
theorem projectionToSpec_eq_comp_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hA : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).projectionToBase (t + 1) :=
    toMarkedSequence_projectionToBase_eq _ hmk (t + 1)
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t :=
    hA.trans (BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) t)
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
        T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
          T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

private def unionSupportsExcept {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) : Set ↥Y :=
  ⋃ i : Fin L.length, ⋃ (_ : (i : ℕ) ≠ j), ((L.get i).support : Set ↥Y)

/- English proof (authored)
The union includes the support at every valid index other than j. Use the given index i to witness membership for any point of its support.
-/
private theorem support_subset_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j i : ℕ)
    (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept L j := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, Set.mem_iUnion.2 ⟨hij, hx⟩⟩

/- English proof (authored)
Membership in the union yields an index in the finite index set. The corresponding inner union yields both the condition that this index differs from j and membership in its support.
-/
private theorem exists_mem_support_of_mem_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ)
    {x : ↥Y} (hx : x ∈ unionSupportsExcept L j) :
    ∃ i : ℕ, ∃ h : i < L.length, i ≠ j ∧ x ∈ ((L[i].support : Set ↥Y)) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨h1, h2⟩ := Set.mem_iUnion.1 hi
  exact ⟨i.1, i.2, h1, h2⟩

/- English proof (authored)
The index set of proofs of the proposition has at most one element and is therefore finite. Every member is the given closed set, so their finite union is closed.
-/
private theorem isClosed_iUnion_prop {α : Type u} [TopologicalSpace α] {p : Prop} {A : Set α}
    (h : IsClosed A) : IsClosed (⋃ _ : p, A) :=
  isClosed_iUnion_of_finite fun _ => h

/- English proof (authored)
For each list index the conditional union is closed, since the support is closed and the condition has at most one witness. The outer union is finite, so it is closed as well.
-/
private theorem isClosed_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) :
    IsClosed (unionSupportsExcept L j) := by
  refine isClosed_iUnion_of_finite ?_
  intro i
  exact isClosed_iUnion_prop ((L.get i).support).2

/- English proof (authored)
Evaluate the equality of composite morphisms at the given point and expand each composite as successive application of its maps.
-/
private theorem apply_eq_apply_of_comp_eq {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ D) (g' : D ⟶ C) (e : f ≫ g = f' ≫ g') (x : ↥A) : ⇑g (⇑f x) = ⇑g' (⇑f' x) :=
  congrArg (fun m : A ⟶ C => ⇑m x) e

/- English proof (authored)
The boundary locus is the union of supports over all entries of the boundary list. A point in the union has a witnessing entry containing it, and such an entry in turn puts the point in the union.
-/
private theorem mem_boundaryLocus_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) (x : ↥(s.schemeAt t)) :
    x ∈ MarkedSequenceOfBlowups.boundaryLocus s t ↔
      ∃ D ∈ s.boundary t, x ∈ ((D.support : Set ↥(s.schemeAt t))) := by
  constructor
  · intro hx
    unfold MarkedSequenceOfBlowups.boundaryLocus at hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨D, hD, hxD⟩
  · rintro ⟨D, hD, hxD⟩
    unfold MarkedSequenceOfBlowups.boundaryLocus
    exact Set.mem_iUnion₂.2 ⟨D, hD, hxD⟩

/- English proof (authored)
Both sets are defined by taking the supports of the stage-t boundary entries at indices different from j and forming their union.
-/
private theorem otherBoundaryLocus_eq_otherLocusOfList {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    MarkedSequenceOfBlowups.otherBoundaryLocus S j t = unionSupportsExcept (S.boundary t) j := rfl

/- English proof (authored)
An index in the first list remains valid after a second list is appended, and the entry it selects is unchanged. Since the index differs from j, the same support occurs in the union for the concatenated list.
-/
private theorem support_subset_otherLocusOfList_append_left {Y : Scheme.{u}} (L M : List Y.IdealSheafData)
    (j i : ℕ) (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ M) j := by
  have h1 : i < (L ++ M).length := by
    rw [List.length_append]
    omega
  have h2 := support_subset_otherLocusOfList (L ++ M) j i h1 hij
  rwa [List.getElem_append_left hi] at h2

/- English proof (authored)
The appended entry occurs at the old list length. This index differs from j because j lies in the old list, so the support of the appended entry appears in the union.
-/
private theorem support_subset_otherLocusOfList_append_singleton {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (e : Y.IdealSheafData) (j : ℕ) (hj : j < L.length) :
    ((e.support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ [e]) j := by
  have h1 : L.length < (L ++ [e]).length := by
    rw [List.length_append]
    simp
  have h2 := support_subset_otherLocusOfList (L ++ [e]) j L.length h1 (by omega)
  have h3 : (L ++ [e])[L.length]'h1 = e := by simp
  rwa [h3] at h2

/- English proof (authored)
Specialize the commuting projection square to stage zero. The ambient and divisor stage-zero projections are the forward maps of their initial isomorphisms, so the two paths in the square are the stated composites.
-/
private theorem embeddingIntoAmbient_zero_comp_isoObjZero_hom (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom =
      s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj I₀ E₀ s hpr 0
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase, MarkedSequenceOfBlowups.projectionToBase_zero,
    BlowupSequenceData.projectionToBase_zero] at h
  exact h

/- English proof (authored)
The ambient center is defined as the scheme-theoretic image of the divisor center under the stage embedding. Since the stage embedding is a closed immersion, pulling its image ideal back along the immersion recovers the divisor center ideal.
-/
private theorem comap_embeddingIntoAmbient_center_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
  have := instIsClosedImmersionPushedEmb hres hno T j hj I₀ E₀ s hpr t
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
  exact Blowup.comap_schemeImageIdeal (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

/- English proof (authored)
The inverse image of the ambient center support is the support of its ideal pulled back to the stage divisor. The pullback of the ambient center ideal is exactly the divisor center ideal, so this inverse image is the divisor center support.
-/
private theorem preimage_support_center_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support : Set _)) =
      (((s.center t).support : Set ↥(s.schemeAt t))) := by
  ext x
  have h : x ∈ (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).support ↔
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) x ∈
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support) : Set _) :=
    Scheme.IdealSheafData.mem_support_comap ..
  rw [comap_embeddingIntoAmbient_center_ambientBlowupSeq] at h
  exact h.symm

/- English proof (authored)
The boundary subscheme is closed in the Noetherian ambient scheme. Its inclusion is quasi-compact and locally of finite type, which makes the boundary subscheme Noetherian.
-/
private theorem isNoetherian_boundary_subscheme (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) :
    AlgebraicGeometry.IsNoetherian (T.boundary.get ⟨j, hj⟩).subscheme := by
  have : AlgebraicGeometry.LocallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι :=
    inferInstance
  have : AlgebraicGeometry.QuasiCompact (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
  exact isNoetherian_of_locallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι

/- English proof (authored)
The chosen divisor is Noetherian as a closed subscheme of the ambient scheme. The blowup sequence over it preserves Noetherianity at every stage bounded by the sequence length.
-/
private theorem isNoetherian_schemeAt_restrictToBoundaryDivisor (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
  @isNoetherian_schemeAt _ s.toSequenceOfBlowups (isNoetherian_boundary_subscheme T j hj) i hi

/- English proof (authored)
At stage zero any entry of the divisor boundary is obtained by pulling back an entry of the starting ambient boundary with index different from j. The stage-zero projection square therefore puts the image of any point of that support in the corresponding ambient support.

For a successor stage, consider first a strict transform of an old divisor-boundary entry. Away from the inverse image of the center, the projection of a point in the transform lies in the old support. By induction its ambient image lies in an old ambient boundary support with index different from j. The transition square and the equality of the inverse image of the ambient center support with the divisor center support put the point's ambient lift in the strict transform of that ambient entry. This entry keeps its index. The ambient union of these supports is closed, as is its inverse image in the divisor. Taking the closure of the inverse-image locus off the center proves the same inclusion for the whole strict-transform support.

For the new exceptional entry, its support is the inverse image of the divisor center support along the transition. The same transition square puts its image in the ambient exceptional support. The ambient exceptional entry is appended after the old entries, so its index differs from j. These are all successor boundary entries.
-/
private theorem boundaryLocus_subset_preimage_otherLocus (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hjE : j < E₀.length) :
    ∀ t, t ≤ s.length →
      MarkedSequenceOfBlowups.boundaryLocus s t ⊆
        ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff s 0 x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_zero] at hD
      obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
      have hD₀' : D₀ ∈ List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (List.take (T.boundary.length - 1) (E₀.eraseIdx j)) := hD₀
      obtain ⟨D₁, hD₁, rfl⟩ := List.mem_map.1 hD₀'
      have hD₁' : D₁ ∈ E₀.eraseIdx j := List.mem_of_mem_take hD₁
      obtain ⟨i, hi, hij, hget⟩ := List.mem_eraseIdx_iff_getElem.1 hD₁'
      subst hget
      have hlen0 : i < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length := by
        rw [BlowupSequenceData.boundary_length]
        omega
      have hentry0 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0)[i]'hlen0
          = (E₀[i]'hi).comap (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom := by
        simp [BlowupSequenceData.boundary_zero]
      have hmem0 : x ∈ ((((E₀[i]'hi).comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
          s.isoZero.hom).support : Set _) := hxD
      have hmem1 := Scheme.IdealSheafData.mem_support_comap.mp hmem0
      have hmem2 := Scheme.IdealSheafData.mem_support_comap.mp hmem1
      have hkey := apply_eq_apply_of_comp_eq (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0)
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom s.isoZero.hom
        (T.boundary.get ⟨j, hj⟩).subschemeι
        (embeddingIntoAmbient_zero_comp_isoObjZero_hom hres hno T j hj I₀ E₀ s hpr) x
      have hmem3 : ⇑(ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom
          (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x) ∈ (E₀[i]'hi).support := by
        rw [hkey]
        exact hmem2
      show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x ∈
        unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0) j
      refine support_subset_otherLocusOfList _ j i hlen0 hij ?_
      rw [hentry0]
      exact Scheme.IdealSheafData.mem_support_comap.mpr hmem3
  | succ n ih =>
      intro ht x hx
      have hn : n < s.length := ht
      have ihn := ih (Nat.le_of_lt hn)
      have : AlgebraicGeometry.IsNoetherian (s.schemeAt (n + 1)) :=
        isNoetherian_schemeAt_restrictToBoundaryDivisor T j hj I₀ E₀ s (n + 1) hn
      have : AlgebraicGeometry.IsNoetherian
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (n + 1)) :=
        isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (n + 1) hn
      have hmapeq : ∀ y : ↥(s.schemeAt (n + 1)),
          ⇑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y)
            = ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y) := by
        intro y
        exact apply_eq_apply_of_comp_eq _ _ _ _
          (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr n) y
      have hcenter := preimage_support_center_ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr n
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff s (n + 1) x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_succ s n hn] at hD
      rcases List.mem_append.1 hD with hD' | hD'
      · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
        have hCclosed : IsClosed (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) ⁻¹'
            unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j) :=
          (isClosed_otherLocusOfList _ _).preimage
            (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)).continuous
        rw [support_strictTransform_eq_closure_sdiff (s.transitionMapSucc n) (s.center n) D₀] at hxD
        refine hCclosed.closure_subset_iff.2 ?_ hxD
        intro y hy
        have hy1 : ⇑(s.transitionMapSucc n) y ∈ (D₀.support : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hy.1
        have hy2 : ⇑(s.transitionMapSucc n) y ∉ (((s.center n).support) : Set _) := fun hcon =>
          hy.2 ((Scheme.IdealSheafData.mem_support_comap ..).2 hcon)
        have hIH0 := ihn ((mem_boundaryLocus_iff s n _).2 ⟨D₀, hD₀, hy1⟩)
        have hIH : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j := hIH0
        obtain ⟨i, hi, hij, hmem⟩ :=
          exists_mem_support_of_mem_otherLocusOfList ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j hIH
        have hnotZ : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∉ ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n).support : Set _)) := by
          intro hcon
          exact hy2 ((Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) y)).1 hcon)
        have hstep : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
            ((Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi)).support : Set _) := by
          rw [support_strictTransform_eq_closure_sdiff]
          refine subset_closure ?_
          refine ⟨?_, ?_⟩
          · refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
            rw [hmapeq y]
            exact hmem
          · intro hcon
            have hcon' := (Scheme.IdealSheafData.mem_support_comap ..).1 hcon
            rw [hmapeq y] at hcon'
            exact hnotZ hcon'
        have hlen : i < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map]
          exact hi
        have hentry : (List.map
              (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))[i]'hlen
            = Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi) := by
          simp
        have hfin := support_subset_otherLocusOfList_append_left
          (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))
          [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)] j i hlen hij
        rw [hentry] at hfin
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact hfin hstep
      · have hDe : D = Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) := by
          simpa using hD'
        subst hDe
        rw [Blowup.exceptionalIdeal_eq_comap] at hxD
        have hxD' : ⇑(s.transitionMapSucc n) x ∈ (((s.center n).support) : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hxD
        have hjlen : j < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map, BlowupSequenceData.boundary_length]
          omega
        have hmem : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
            ((Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)).support : Set _) := by
          rw [Blowup.exceptionalIdeal_eq_comap]
          refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
          rw [hmapeq x]
          exact (Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) x)).2 hxD'
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact support_subset_otherLocusOfList_append_singleton _ _ j hjlen hmem

/- English proof (authored)
The pushed marked sequence uses the boundaries obtained by starting with the original ambient boundary and applying the boundary recursion of the ambient blowup data. The equality identifies the stage-t lists in these two descriptions.
-/
private theorem ambientMarkedSeq_boundary (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

/- English proof (authored)
The marked sequence is formed from the prepended blowup data with the original boundary. By the boundary formula for that construction, its stage-t boundary equals the iterated boundary of the prepended data from the original list.
-/
private theorem prependedAmbientSeq_boundary (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary t =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

/- English proof (authored)
At the first prepended stage the boundary is the lower ambient boundary transported through the initial ambient isomorphism, which is the ambient stage-zero boundary. At each later stage the prepended morphism and center are the corresponding ambient morphism and center with the index shifted by one. Equal preceding boundaries give equal strict transforms and equal appended exceptional entries. Induction proves the formula.
-/
private theorem prepend_boundary_succ_eq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
        (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t := by
  induction t with
  | zero =>
      rw [boundary_prepend_ambientBlowupSeq_one, BlowupSequenceData.boundary_zero]
  | succ m ih =>
      rw [BlowupSequenceData.boundary_succ, ih, BlowupSequenceData.boundary_succ, BlowupSequenceData.prepend_blowupMorphism_succ,
        BlowupSequenceData.prepend_center_succ]
      rfl

/- English proof (authored)
Without a preparatory blowup, the lower ambient boundary is the original boundary, so j remains an admissible index. Apply the general boundary-locus inclusion. The stage boundary of the pushed marked sequence is the iterated ambient boundary from that same original list. Taking the union over indices other than j gives precisely its other boundary locus.
-/
theorem boundaryLocus_subset_preimage_otherBoundaryLocus (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t := by
  have hlowerEq : lowerBoundaryWithoutBlowup T = T.boundary := by simp [lowerBoundaryWithoutBlowup_eq]
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by
    rw [hlowerEq]
    exact hj
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr hjE t (le_of_lt ht)
  have h1 : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
        (lowerBoundaryWithoutBlowup T) t := by
    rw [ambientMarkedSeq_boundary]
    exact congrArg
      (fun E => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom E t)
      hlowerEq.symm
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t
      = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
          (lowerBoundaryWithoutBlowup T) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList _ j t).trans (congrArg (fun L => unionSupportsExcept L j) h1)
  rw [hset]
  exact hmain

/- English proof (authored)
The preparatory blowup takes strict transforms of all original boundary entries and appends one exceptional entry, so j still lies in the lower ambient list. Apply the general inclusion to this lower boundary. The shifted boundary recursion identifies the ambient stage-t list with the prepended marked sequence's list at stage t+1. Their unions of supports at indices different from j therefore agree.
-/
theorem boundaryLocus_subset_preimage_otherBoundaryLocus_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1) := by
  have hjE : j < (lowerBoundaryAfterBlowup T j hj).length := by
    show j < (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
      (List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]).length
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr hjE t (le_of_lt ht)
  have h1 : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom
        (lowerBoundaryAfterBlowup T j hj) t := by
    rw [prependedAmbientSeq_boundary, prepend_boundary_succ_eq]
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1)
      = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList _ j (t + 1)).trans (congrArg (fun L => unionSupportsExcept L j) h1)
  rw [hset]
  exact hmain

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
