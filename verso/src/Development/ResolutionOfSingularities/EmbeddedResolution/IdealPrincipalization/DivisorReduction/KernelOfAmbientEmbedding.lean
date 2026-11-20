import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
At zero the embedding is the lower initial isomorphism followed by the original closed immersion. Precomposition with an isomorphism preserves the kernel ideal, so its kernel is the original kernel. The ambient initial isomorphism is the identity, hence pulling that kernel back along it fixes the ideal.
-/
theorem ker_embeddingIntoAmbientBlowupSequence_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0) =
      (AlgebraicGeometry.Scheme.Hom.ker ι).comap
        (ambientBlowupSequence ι s hres hno hcen).isoZero.hom := by
  have h1 : embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι :=
    embeddingIntoAmbientBlowupSequence_zero ι s hres hno hcen
  have h2 : (AlgebraicGeometry.Scheme.Hom.ker ι).comap
      (ambientBlowupSequence ι s hres hno hcen).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker ι := by
    rw [ambientBlowupSequence_isoObjZero]
    exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  rw [h1, h2]
  exact Scheme.Hom.ker_comp_of_isIso s.isoZero.hom ι

/- English proof (authored)
At zero the embedding kernel is the pullback of the original kernel along the initial ambient isomorphism. The chosen boundary entry is the original kernel, so its initial pullback is equal to that kernel at zero. At a successor, the new embedding kernel is the strict transform of the preceding kernel. The chosen boundary entry is still within the preceding list because the boundary length only grows. Its new value is the strict transform of its preceding value, since the new exceptional ideal is appended. Induction identifies the two ideals.
-/
private theorem forall_le_ker_embeddingIntoAmbient_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι) :
    ∀ t : ℕ, t ≤ s.length →
      ∀ hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length,
        AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
          ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ := by
  intro t
  induction t with
  | zero =>
      intro _ hjt
      simp only [List.get_eq_getElem] at hE ⊢
      rw [ker_embeddingIntoAmbientBlowupSequence_zero]
      simp only [BlowupSequenceData.boundary_zero, List.getElem_map, hE]
  | succ n ih =>
      intro hn hjt
      have hn' : n < s.length := hn
      have hjn : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E n).length := by
        rw [BlowupSequenceData.boundary_length]; omega
      rw [ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen n hn', ih (le_of_lt hn') hjn]
      simp only [List.get_eq_getElem, BlowupSequenceData.boundary_succ]
      rw [List.getElem_append_left (by simpa using hjn), List.getElem_map]

/- English proof (authored)
The stagewise induction identifies the kernel with the transformed original boundary entry at every stage through the length. Evaluate it at the given stage and index.
-/
theorem ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι)
    (t : ℕ) (ht : t ≤ s.length)
    (hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
      ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ :=
  forall_le_ker_embeddingIntoAmbient_eq_boundary_get ι s hres hno hcen E j hj hE t ht hjt

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

/- English proof (authored)
Use the general zero-stage kernel formula with the original closed immersion equal to the selected divisor inclusion. Its kernel is the selected boundary ideal. The ambient marked conversion retains the original initial isomorphism, giving the asserted pullback.
-/
theorem ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr 0) =
      (T.boundary.get ⟨j, hj⟩).comap (pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  exact h0

/- English proof (authored)
The unprepended ambient embedding at zero has kernel equal to the boundary ideal pulled back along the unprepended initial isomorphism. The prepended sequence starts with the identity isomorphism and its first transition is precisely the unprepended initial isomorphism. Thus the two successive pullbacks in the assertion equal the original single pullback.
-/
theorem ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0) =
      ((T.boundary.get ⟨j, hj⟩).comap
          (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0) := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  have hA : (T.boundary.get ⟨j, hj⟩).comap
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0
      = (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).isoZero.hom := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism,
      BlowupSequenceData.prepend_blowupMorphism_zero]
    exact rfl
  rw [hA, hB]
  exact h0

/- English proof (authored)
The embedding kernel at the given stage is the transformed entry corresponding to the chosen original boundary divisor. The marked ambient sequence has that transformed boundary list, and its length is the lower sequence length, so the stage is within range. A marked sequence from an admissible input preserves strict normal crossings of its boundary. Each entry of that boundary therefore defines a smooth divisor for its stage structure map, including the embedding kernel.
-/
theorem isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hob : T.IsOrderBoundedByMult) (_hbal : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length) (_hpre : containedComponentsIdeal T j hj = ⊤)
    (_hlow : (restrictToDivisor T j hj).IsAdmissible)
    [AlgebraicGeometry.IsNoetherian T.scheme] (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (t : ℕ) (ht : t ≤ s.length) :
    IsSmoothDivisor ((pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
      (AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t)) := by
  have hjt : j < ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).length := by
    rw [BlowupSequenceData.boundary_length]; omega
  have htS : t ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact ht
  have hker : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) =
      ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).get
          ⟨j, hjt⟩ :=
    ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr T.boundary j hj
      (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _).symm t htS hjt
  have hbd : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    exact rfl
  have hpl : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).length =
      s.toSequenceOfBlowups.length := by
    have hh := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length] at hh
    exact hh
  have htlen : t ≤ (pushedMarkedSeq hres hno T j hj s hpr hmk).toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hpl]
    exact ht
  have hsnc := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hV
    (pushedMarkedSeq hres hno T j hj s hpr hmk) t htlen
  have key : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [hker]
    exact List.getElem_mem _
  have key2 : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t := by
    rw [hbd]
    exact key
  exact ((inStrictNormalCrossingPosition_iff _ _).mp hsnc).1 _ key2

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
