import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def BlowupPreservesNoetherian : Prop :=
  ∀ (X X' : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] (π : X' ⟶ X)
    (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z → AlgebraicGeometry.IsNoetherian X'

structure AmbientEmbedding {S : Scheme.{u}} (s : BlowupSequenceData S) (n : ℕ) : Type (u + 1) where
  ambient : Scheme.{u}
  emb : s.obj n ⟶ ambient
  emb_isClosedImmersion : AlgebraicGeometry.IsClosedImmersion emb
  isNoetherian_ambient_of_le_length : n ≤ s.length → AlgebraicGeometry.IsNoetherian ambient

/- English proof (authored)
The stage-zero isomorphism is a closed immersion, and the original embedding is a closed immersion by hypothesis. The property is preserved by composition.
-/
private theorem isClosedImmersion_isoObjZero_hom_comp {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (s : BlowupSequenceData S) :
    AlgebraicGeometry.IsClosedImmersion (s.isoZero.hom ≫ ι) := by
  have : AlgebraicGeometry.IsClosedImmersion s.isoZero.hom := inferInstance
  infer_instance

/- English proof (authored)
The canonical projection is a blowup along the given ideal. The assumed Noetherian preservation for blowups applies because its target is Noetherian.
-/
private theorem isNoetherian_blowup_of_isNoetherian (hno : BlowupPreservesNoetherian.{u})
    {A : Scheme.{u}} (hA : AlgebraicGeometry.IsNoetherian A) (Z : A.IdealSheafData) :
    AlgebraicGeometry.IsNoetherian (Blowup.blowup Z) := by
  have := hA
  exact hno A (Blowup.blowup Z) (Blowup.blowup.proj Z) Z (Blowup.blowup.isBlowupAlongIdealSheaf_proj Z)

/- English proof (authored)
The image ideal sheaf is the image of the original ideal along the closed immersion. Pulling this image back along the closed immersion recovers the original ideal by the ideal image formula for closed immersions.
-/
private theorem comap_imageIdealSheaf_of_isClosedImmersion {S' A : Scheme.{u}} (σ : S' ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion σ] (J : S'.IdealSheafData) :
    (imageIdealSheaf σ J).comap σ = J := by
  have h : imageIdealSheaf σ J = J.map σ := rfl
  rw [h]
  exact Blowup.comap_map_of_isClosedImmersion σ J

/- English proof (authored)
The support of a pulled-back ideal is the inverse image of the original support. In particular, the indicated inverse image is contained in it.
-/
private theorem preimage_support_subset_support_comap {S' A : Scheme.{u}} (σ : S' ⟶ A) (Z : A.IdealSheafData) :
    σ.base ⁻¹' (Z.support : Set ↥A) ⊆ ((Z.comap σ).support : Set ↥S') := by
  simp [Scheme.IdealSheafData.support_comap]

/- English proof (authored)
Push the center ideal forward through the closed immersion. Its pullback is the original center ideal. If an irreducible component of the embedded scheme mapped entirely into the pushed-forward center support, the support pullback identity would put it inside the original center support, contrary to the hypothesis. The strict-transform blowup theorem therefore identifies the ambient strict transform of the embedded scheme as a blowup along the original center. The given source is also such a blowup, so their universal properties give mutually inverse maps over the embedded scheme. Compose this isomorphism with the inclusion of the ambient strict transform. This is a closed immersion compatible with both blowup projections. Its kernel is the strict-transform ideal because the first map is an isomorphism and the second is the inclusion defined by that ideal.
-/
private theorem exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    {S' A : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian A] (σ : S' ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion σ] (J : S'.IdealSheafData) {S'' : Scheme.{u}}
    (f : S'' ⟶ S') (hf : Blowup.IsBlowupAlongIdealSheaf f J)
    (hc : ∀ T ∈ irreducibleComponents ↥S', ¬ T ⊆ (J.support : Set ↥S')) :
    ∃ τ : S'' ⟶ Blowup.blowup (imageIdealSheaf σ J),
      AlgebraicGeometry.IsClosedImmersion τ ∧
      τ ≫ Blowup.blowup.proj (imageIdealSheaf σ J) = f ≫ σ ∧
      τ.ker = Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) σ.ker := by
  have hπ : Blowup.IsBlowupAlongIdealSheaf (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) :=
    Blowup.blowup.isBlowupAlongIdealSheaf_proj _
  have hcomap : (imageIdealSheaf σ J).comap σ = J := comap_imageIdealSheaf_of_isClosedImmersion σ J
  have hsupp : ∀ T ∈ irreducibleComponents ↥S',
      ¬ (σ.base '' T) ⊆ ((imageIdealSheaf σ J).support : Set ↥A) := by
    intro T hT hsub
    refine hc T hT ?_
    have h2 := (Set.image_subset_iff.mp hsub).trans (preimage_support_subset_support_comap σ (imageIdealSheaf σ J))
    rwa [hcomap] at h2
  obtain ⟨ψ, hψ1, hψ2⟩ := hres A (Blowup.blowup (imageIdealSheaf σ J)) S' σ
    (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) hπ hsupp
  rw [hcomap] at hψ2
  have hab : hψ2.lift f hf.1 ≫ ψ = f := hψ2.lift_comp f hf.1
  have hba : hf.lift ψ hψ2.1 ≫ f = ψ := hf.lift_comp ψ hψ2.1
  have hid1 : hψ2.lift f hf.1 ≫ hf.lift ψ hψ2.1 = 𝟙 S'' := by
    refine hf.hom_ext hf.1 ?_ (Category.id_comp f)
    rw [Category.assoc, hba, hab]
  have hid2 : hf.lift ψ hψ2.1 ≫ hψ2.lift f hf.1 = 𝟙 _ := by
    refine hψ2.hom_ext hψ2.1 ?_ (Category.id_comp ψ)
    rw [Category.assoc, hab, hba]
  have : IsIso (hψ2.lift f hf.1) := ⟨⟨hf.lift ψ hψ2.1, hid1, hid2⟩⟩
  refine ⟨hψ2.lift f hf.1 ≫
      (Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) σ.ker).subschemeι,
    inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hψ1, ← Category.assoc, hab]
  · rw [Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_subschemeι _

/- English proof (authored)
At a valid stage the transition is a blowup of the specified center. The ambient is Noetherian and hence locally Noetherian. Apply the result on embedding a blowup into the ambient blowup of the image ideal, using the given closed immersion and center condition.
-/
private theorem exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (_hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    ∃ τ : s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ (s.center n)),
      AlgebraicGeometry.IsClosedImmersion τ ∧
      τ ≫ Blowup.blowup.proj (imageIdealSheaf σ (s.center n)) = s.map n ≫ σ ∧
      τ.ker = Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ (s.center n)))
          (imageIdealSheaf σ (s.center n)) σ.ker := by
  have := hσ
  have := hA
  have : AlgebraicGeometry.IsLocallyNoetherian A := inferInstance
  exact exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf hres σ (s.center n) (s.map n) (s.isBlowup n hn) hc

private def embeddingIntoAmbientBlowup (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ (s.center n)) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose

/- English proof (authored)
The chosen next-stage embedding is the one supplied by the ambient blowup comparison, which is a closed immersion.
-/
private theorem isClosedImmersion_embeddingIntoBlowupImageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbientBlowup hres hno s n hn A σ hσ hA hc) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose_spec.1

/- English proof (authored)
The chosen immersion identifies the source blowup with the strict transform in the ambient blowup over the preceding embedded scheme. Its projection to the old ambient is therefore the source transition followed by the old embedding.
-/
private theorem embeddingIntoBlowupImageIdealSheaf_comp_proj (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    embeddingIntoAmbientBlowup hres hno s n hn A σ hσ hA hc ≫ Blowup.blowup.proj (imageIdealSheaf σ (s.center n)) =
      s.map n ≫ σ :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose_spec.2.1

/- English proof (authored)
The chosen new embedding has image the ambient strict transform of the preceding embedded scheme. Its defining kernel is the strict transform of the preceding embedding ideal.
-/
private theorem ker_embeddingIntoBlowupImageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    (embeddingIntoAmbientBlowup hres hno s n hn A σ hσ hA hc).ker =
      Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ (s.center n)))
        (imageIdealSheaf σ (s.center n)) σ.ker :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose_spec.2.2

private def ambientEmbeddingZero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) : AmbientEmbedding s 0 where
  ambient := X
  emb := s.isoZero.hom ≫ ι
  emb_isClosedImmersion := isClosedImmersion_isoObjZero_hom_comp ι s
  isNoetherian_ambient_of_le_length := fun _ => inferInstance

private def ambientEmbeddingSucc (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) :
    Σ t : AmbientEmbedding s (n + 1), (t.ambient ⟶ st.ambient) :=
  if h : n < s.length then
    ⟨{ ambient := Blowup.blowup (imageIdealSheaf st.emb (s.center n))
       emb := embeddingIntoAmbientBlowup hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
         (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
       emb_isClosedImmersion := isClosedImmersion_embeddingIntoBlowupImageIdealSheaf hres hno s n h st.ambient st.emb
         st.emb_isClosedImmersion (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
       isNoetherian_ambient_of_le_length := fun _ =>
         isNoetherian_blowup_of_isNoetherian hno (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h))
           (imageIdealSheaf st.emb (s.center n)) },
     Blowup.blowup.proj (imageIdealSheaf st.emb (s.center n))⟩
  else
    ⟨{ ambient := s.obj (n + 1)
       emb := 𝟙 (s.obj (n + 1))
       emb_isClosedImmersion := inferInstance
       isNoetherian_ambient_of_le_length := fun hle => absurd (Nat.lt_of_succ_le hle) h },
     s.map n ≫ st.emb⟩

/- English proof (authored)
At an active step the construction uses the canonical projection from the blowup of the image of the center ideal. This projection is a blowup along that image ideal.
-/
private theorem isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) (h : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSucc hres hno s hcen n st).2 (imageIdealSheaf st.emb (s.center n)) := by
  unfold ambientEmbeddingSucc
  rw [dif_pos h]
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj _

/- English proof (authored)
At an active step the compatibility follows from the chosen embedding into the ambient blowup. After the active range, the new embedding is the identity and the new ambient map is the source transition followed by the old embedding. The same equality then follows from the identity law.
-/
private theorem succAmbientEmbedding_comp_blowupMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) :
    (ambientEmbeddingSucc hres hno s hcen n st).1.emb ≫ (ambientEmbeddingSucc hres hno s hcen n st).2 =
      s.map n ≫ st.emb := by
  unfold ambientEmbeddingSucc
  by_cases h : n < s.length
  · rw [dif_pos h]
    exact embeddingIntoBlowupImageIdealSheaf_comp_proj hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
      (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
  · rw [dif_neg h]
    exact Category.id_comp _

/- English proof (authored)
At a valid step the new embedding is the chosen strict-transform embedding, and the ambient map is the canonical blowup of the image center. The kernel calculation for that embedding gives the stated strict transform.
-/
private theorem ker_succAmbientEmbedding_eq_strictTransform (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) (h : n < s.length) :
    (ambientEmbeddingSucc hres hno s hcen n st).1.emb.ker =
      Blowup.strictTransform (ambientEmbeddingSucc hres hno s hcen n st).2
        (imageIdealSheaf st.emb (s.center n)) st.emb.ker := by
  unfold ambientEmbeddingSucc
  rw [dif_pos h]
  exact ker_embeddingIntoBlowupImageIdealSheaf hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
    (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)

private def ambientEmbedding {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    ∀ n : ℕ, AmbientEmbedding s n := fun n =>
  Nat.rec (motive := fun n => AmbientEmbedding s n) (ambientEmbeddingZero ι s)
    (fun m st => (ambientEmbeddingSucc hres hno s hcen m st).1) n

private def ambientEmbeddingSuccMap {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    (ambientEmbedding ι s hres hno hcen (n + 1)).ambient ⟶ (ambientEmbedding ι s hres hno hcen n).ambient :=
  (ambientEmbeddingSucc hres hno s hcen n (ambientEmbedding ι s hres hno hcen n)).2

/- English proof (authored)
The transition map of the recursive ambient sequence is the successor ambient map at the chosen stage. At every valid index this map is a blowup along the image of the current center.
-/
private theorem isBlowupAlongIdealSheaf_ambientBlowupMorphism {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSuccMap ι s hres hno hcen n)
      (imageIdealSheaf (ambientEmbedding ι s hres hno hcen n).emb (s.center n)) :=
  isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism hres hno s hcen n (ambientEmbedding ι s hres hno hcen n) hn

def ambientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) : BlowupSequenceData X where
  length := s.length
  obj := fun n => (ambientEmbedding ι s hres hno hcen n).ambient
  map := fun n => ambientEmbeddingSuccMap ι s hres hno hcen n
  isoZero := Iso.refl X
  center := fun n => imageIdealSheaf (ambientEmbedding ι s hres hno hcen n).emb (s.center n)
  isBlowup := fun n hn => isBlowupAlongIdealSheaf_ambientBlowupMorphism ι s hres hno hcen n hn

def embeddingIntoAmbientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    s.obj n ⟶ (ambientBlowupSequence ι s hres hno hcen).obj n :=
  (ambientEmbedding ι s hres hno hcen n).emb

@[simp]
/- English proof (authored)
The ambient blowup sequence is assigned the same number of active steps as the original sequence.
-/
theorem ambientBlowupSequence_length {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).length = s.length := rfl

/- English proof (authored)
The recursive ambient sequence starts with the given ambient scheme.
-/
theorem ambientBlowupSequence_schemeAt_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).obj 0 = X := rfl

/- English proof (authored)
Since the initial ambient is the given ambient itself, the construction uses its identity isomorphism at stage zero.
-/
theorem ambientBlowupSequence_isoObjZero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).isoZero = Iso.refl X := rfl

@[simp]
/- English proof (authored)
The ambient center at a stage is defined by taking the image of the original center ideal through its stage embedding.
-/
theorem ambientBlowupSequence_center {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    (ambientBlowupSequence ι s hres hno hcen).center n =
      imageIdealSheaf (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) (s.center n) := rfl

/- English proof (authored)
The initial ambient is Noetherian, and each actual subsequent ambient arises by blowing up the preceding Noetherian ambient along the image center. The preservation assumption gives Noetherianity throughout the stated range.
-/
theorem isNoetherian_ambientBlowupSequence_schemeAt {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n ≤ s.length) :
    AlgebraicGeometry.IsNoetherian ((ambientBlowupSequence ι s hres hno hcen).obj n) :=
  (ambientEmbedding ι s hres hno hcen n).isNoetherian_ambient_of_le_length hn

/- English proof (authored)
Every stage of the recursive ambient construction supplies a closed immersion. At zero it is the original immersion composed with the initial isomorphism, at an actual successor it is the strict-transform immersion, and beyond the active stages the construction uses the identity.
-/
theorem isClosedImmersion_embeddingIntoAmbientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) :=
  (ambientEmbedding ι s hres hno hcen n).emb_isClosedImmersion

/- English proof (authored)
The initial embedding is defined as the original sequence's stage-zero isomorphism followed by the given ambient immersion.
-/
theorem embeddingIntoAmbientBlowupSequence_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι := rfl

/- English proof (authored)
The two maps at consecutive stages are the recursive embeddings, with the ambient transition given by the successor construction. Its compatibility with the original transition is the successor commutative square already established.
-/
theorem embeddingIntoAmbientBlowupSequence_succ_comp_map {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1) ≫ (ambientBlowupSequence ι s hres hno hcen).map n =
      s.map n ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen n :=
  succAmbientEmbedding_comp_blowupMorphism hres hno s hcen n (ambientEmbedding ι s hres hno hcen n)

/- English proof (authored)
At this actual step, the next stage is embedded as the strict transform of the previous stage in the ambient blowup. The successor kernel formula therefore identifies its ideal with the strict transform along the ambient map and center of that step.
-/
theorem ker_embeddingIntoAmbientBlowupSequence_succ {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n < s.length) :
    (embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1)).ker =
      Blowup.strictTransform ((ambientBlowupSequence ι s hres hno hcen).map n)
        ((ambientBlowupSequence ι s hres hno hcen).center n)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n).ker :=
  ker_succAmbientEmbedding_eq_strictTransform hres hno s hcen n (ambientEmbedding ι s hres hno hcen n) hn

/- English proof (authored)
The two sequences have equal length. Take the recursive closed immersion at every stage. At zero it agrees with the original immersion through the initial isomorphisms. The successor squares commute by the stage compatibility. Each ambient center is the image of the original center, and the defining ideal of each successor embedding is the corresponding strict transform. These are the required pushforward comparison data.
-/
theorem isPushforwardBlowupSeq_ambientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups := by
  refine ⟨rfl, ⟨fun i _ => embeddingIntoAmbientBlowupSequence ι s hres hno hcen i,
    fun i _ => isClosedImmersion_embeddingIntoAmbientBlowupSequence ι s hres hno hcen i, ?_, ?_, ?_, ?_⟩⟩
  · show (s.isoZero.hom ≫ ι) ≫ 𝟙 X = s.isoZero.hom ≫ ι
    exact Category.comp_id _
  · intro i hi
    show embeddingIntoAmbientBlowupSequence ι s hres hno hcen (i + 1) ≫
        (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.transitionMapSucc i =
      s.toSequenceOfBlowups.transitionMapSucc i ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen i
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact embeddingIntoAmbientBlowupSequence_succ_comp_map ι s hres hno hcen i
  · intro i _
    rfl
  · intro i hi
    show (embeddingIntoAmbientBlowupSequence ι s hres hno hcen (i + 1)).ker =
      Blowup.strictTransform ((ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.transitionMapSucc i)
        ((ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.center i)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen i).ker
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen i hi

end FunctorialResolution.EmbeddedResolution
