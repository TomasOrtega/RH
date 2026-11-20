import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

open scoped Classical

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

def prependSchemeAt {X : Scheme.{u}} (d : BlowupSequenceData X) : ℕ → Scheme.{u}
  | 0 => X
  | (n + 1) => d.obj n

def prependMap {X : Scheme.{u}} (d : BlowupSequenceData X) :
    (i : ℕ) → d.prependSchemeAt (i + 1) ⟶ d.prependSchemeAt i
  | 0 => d.isoZero.hom
  | (n + 1) => d.map n

def prependCenter {X : Scheme.{u}} (d : BlowupSequenceData X) (Z : X.IdealSheafData) :
    (i : ℕ) → (d.prependSchemeAt i).IdealSheafData
  | 0 => Z
  | (n + 1) => d.center n

/- English proof (authored)
At index zero the new map is the original initial isomorphism. The given blowup property of the identity along $Z$ is preserved by precomposing it with this isomorphism, so the new first map is a blowup along $Z$. At index $n+1$, the new map and center are the original ones at $n$. The length bound ensures that this original index is a genuine step.
-/
theorem isBlowupAlongIdealSheaf_prependMap {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X) (i : ℕ) (hi : i < d.length + 1) :
    Blowup.IsBlowupAlongIdealSheaf (d.prependMap i) (d.prependCenter Z i) := by
  cases i with
  | zero =>
      have h := hZ.iso_hom_comp d.isoZero
      rw [Category.comp_id] at h
      exact h
  | succ n =>
      exact d.isBlowup n (by omega)

def prepend {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) : BlowupSequenceData X where
  length := d.length + 1
  obj := d.prependSchemeAt
  map := d.prependMap
  isoZero := Iso.refl X
  center := d.prependCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_prependMap Z hZ d i hi

section

variable {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)

/- English proof (authored)
The new sequence keeps all original steps and adds one initial step, so its specified length is the original length plus one.
-/
@[simp] theorem prepend_length : (prepend Z hZ d).length = d.length + 1 := rfl

/- English proof (authored)
By construction, the newly inserted initial stage is the base scheme $X$.
-/
@[simp] theorem prepend_schemeAt_zero : (prepend Z hZ d).obj 0 = X := rfl

/- English proof (authored)
The old stage $n$ is placed at the new stage $n+1$, giving the stage equality.
-/
@[simp] theorem prepend_schemeAt_succ (n : ℕ) : (prepend Z hZ d).obj (n + 1) = d.obj n := rfl

/- English proof (authored)
The new first transition goes from the original initial stage to the base scheme. It is defined to be the forward map of the original initial isomorphism.
-/
@[simp] theorem prepend_blowupMorphism_zero : (prepend Z hZ d).map 0 = d.isoZero.hom := rfl

/- English proof (authored)
At successor index $n+1$, the transition in the prepended sequence is defined to be the original transition at $n$.
-/
@[simp] theorem prepend_blowupMorphism_succ (n : ℕ) : (prepend Z hZ d).map (n + 1) = d.map n := rfl

/- English proof (authored)
The new initial stage is the base itself, and its specified isomorphism to the base is the identity.
-/
@[simp] theorem prepend_isoObjZero : (prepend Z hZ d).isoZero = Iso.refl X := rfl

/- English proof (authored)
The inserted first step uses the supplied center ideal $Z$ on the base scheme.
-/
@[simp] theorem prepend_center_zero : (prepend Z hZ d).center 0 = Z := rfl

/- English proof (authored)
After the inserted center, the center at the new index $n+1$ is the original center at $n$.
-/
@[simp] theorem prepend_center_succ (n : ℕ) : (prepend Z hZ d).center (n + 1) = d.center n := rfl

end

def CentersContainNoComponent {S : Scheme.{u}} (d : BlowupSequenceData S) : Prop :=
  ∀ i, i < d.length → ∀ W ∈ irreducibleComponents ↥(d.obj i),
    ¬ W ⊆ ((d.center i).support : Set ↥(d.obj i))

end BlowupSequenceData

namespace DivisorReduction

noncomputable def containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    T.scheme.IdealSheafData :=
  if h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult} then
    Scheme.Hom.ker
      (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
          ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
              connectedComponent x ⊆
                ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
        (T.boundary.get ⟨j, hj⟩).subschemeι)
  else ⊤

/- English proof (authored)
The chosen boundary components form an open subset by assumption. The definition then takes the kernel of its inclusion into the boundary followed by the boundary inclusion into the ambient scheme.
-/
theorem containedComponentsIdeal_eq_ker (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj =
      Scheme.Hom.ker
        (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
            ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
                connectedComponent x ⊆
                  ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι) := dif_pos h

/- English proof (authored)
The selected union fails the openness condition in the definition. The other branch assigns the unit ideal.
-/
theorem containedComponentsIdeal_eq_top_of_not_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : ¬ IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj = ⊤ := by
  exact dif_neg h

noncomputable def restrictToBoundaryDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
    (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
    (((E₀.eraseIdx j).take (T.boundary.length - 1)).map
      (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))

noncomputable def liftSeqFromDivisor (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if hdn : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧
      AlgebraicGeometry.IsNoetherian T.scheme then
    letI := hdn.2
    if hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData.CentersContainNoComponent then
      if hmk : (pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
          hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary then
        ((pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
            hres hno hpr)).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups
      else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

/- English proof (authored)
The strict dimension inequality and Noetherianity allow the construction to apply the lower-dimensional algorithm. The lower sequence has proper centers, so its ambient lift exists. The transformed ambient sequence satisfies the required marking, so the last test also succeeds. The construction therefore returns that marked sequence.
-/
theorem liftSeqFromDivisor_eq_toMarkedSequence (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme)
    [AlgebraicGeometry.IsNoetherian T.scheme]
    (hdim : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData
        hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    liftSeqFromDivisor hres hno T alg j hj I₀ E₀ pre =
      ((pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData
          hres hno hpr)).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have h1 : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧
      AlgebraicGeometry.IsNoetherian T.scheme := ⟨hdim, inferInstance⟩
  exact (dif_pos h1).trans ((dif_pos hpr).trans (dif_pos hmk))

noncomputable def divisorReductionSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) : T.SequenceOfBlowups :=
  if hj : j < T.boundary.length then
    if orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) then
      emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else
      if containedComponentsIdeal T j hj = ⊤ then
        liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap (𝟙 T.scheme))
          (T.boundary.map (fun D => D.comap (𝟙 T.scheme))) id
      else
        if hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj) then
          liftSeqFromDivisor hres hno T alg j hj
            (residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
              (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult)
            ((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
                (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
              [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)])
            (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb)
        else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

/- English proof (authored)
The divisor index is valid, so the construction reaches the order-locus test. That locus is empty by hypothesis, and the definition returns the empty marked sequence in this case.
-/
theorem divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
    (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    divisorReductionSeq hres hno T alg j = emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_pos hcs]

/- English proof (authored)
The index is valid and the order locus is nonempty. The selected center is unit, so the construction lifts the divisor sequence from the ideal and boundary pulled back along the identity, with no initial step inserted.
-/
theorem divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
    (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj = ⊤) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap (𝟙 T.scheme))
        (T.boundary.map (fun D => D.comap (𝟙 T.scheme))) id := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_pos hZ]

/- English proof (authored)
The valid index and nonempty order locus allow the reduction to proceed. The selected center is nonunit and its identity blowup property is given. Thus the construction uses the residual ideal obtained by dividing off the marked exceptional power and the boundary given by strict transforms with the exceptional ideal appended. The lifted sequence is preceded by the blowup of the selected center.
-/
theorem divisorReductionSeq_eq_liftSeqFromDivisor_prepend (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
    (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj ≠ ⊤) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj
        (residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
          (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult)
        ((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
            (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
          [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)])
        (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb) := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_neg hZ, dif_pos hb]

noncomputable def divisorReductionSeqFromLowerDim (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) : T.SequenceOfBlowups :=
  divisorReductionSeq hres hno T alg j

/- English proof (authored)
The lower-dimensional form is defined by applying the divisor reduction construction with the same algorithm, marked input, and divisor index.
-/
theorem divisorReductionSeqFromLowerDim_eq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) :
    divisorReductionSeqFromLowerDim hres hno T alg j = divisorReductionSeq hres hno T alg j := rfl

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
