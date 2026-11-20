import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartPushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpacePushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

/- English proof (authored)
The ambient enlargement is over the field, so its composite with the new structural map is the old structural map. Precomposing by the old embedding gives the structural map of the embedded scheme.
-/
private theorem emb_comp_comp_eq_of_comp_eq (G : EmbeddingDatum k Y p) {A' : Scheme.{u}}
    (q : A' ⟶ Spec (CommRingCat.of k)) (τ : G.ambient ⟶ A')
    (hτ : τ ≫ q = G.ambientStruct) :
    (G.emb ≫ τ) ≫ q = p := by
  rw [Category.assoc, hτ, G.comp_eq]

def enlargeAmbient (G : EmbeddingDatum k Y p) (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    EmbeddingDatum k Y p :=
  embeddingDatumOfClosedImmersion A' q (G.emb ≫ τ) hker (emb_comp_comp_eq_of_comp_eq G q τ hτ) hsnc

@[simp]
/- English proof (authored)
The enlargement datum takes the specified larger scheme as its ambient scheme.
-/
theorem enlargeAmbient_ambient (G : EmbeddingDatum k Y p) (A' : Scheme.{u})
    [AlgebraicGeometry.IsAffine A'] (q : A' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] [AlgebraicGeometry.LocallyOfFiniteType q]
    [AlgebraicGeometry.QuasiCompact q] (τ : G.ambient ⟶ A')
    [AlgebraicGeometry.IsClosedImmersion τ] (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    (G.enlargeAmbient A' q τ hτ hker hsnc).ambient = A' := rfl

@[simp]
/- English proof (authored)
The enlargement datum equips the larger ambient scheme with the structural morphism given in its inputs.
-/
theorem enlargeAmbient_ambientToSpec (G : EmbeddingDatum k Y p) (A' : Scheme.{u})
    [AlgebraicGeometry.IsAffine A'] (q : A' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] [AlgebraicGeometry.LocallyOfFiniteType q]
    [AlgebraicGeometry.QuasiCompact q] (τ : G.ambient ⟶ A')
    [AlgebraicGeometry.IsClosedImmersion τ] (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    (G.enlargeAmbient A' q τ hτ hker hsnc).ambientStruct = q := rfl

@[simp]
/- English proof (authored)
The enlarged datum is constructed by composing the original embedding with the closed immersion into the larger ambient scheme. Its embedding is exactly this composite.
-/
theorem enlargeAmbient_emb (G : EmbeddingDatum k Y p) (A' : Scheme.{u})
    [AlgebraicGeometry.IsAffine A'] (q : A' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] [AlgebraicGeometry.LocallyOfFiniteType q]
    [AlgebraicGeometry.QuasiCompact q] (τ : G.ambient ⟶ A')
    [AlgebraicGeometry.IsClosedImmersion τ] (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    (G.enlargeAmbient A' q τ hτ hker hsnc).emb = G.emb ≫ τ := rfl

/- English proof (authored)
The ideal sheaf of the image under a composite is the image ideal sheaf of the first kernel along the second map. Since the first map is a closed immersion, applying the kernel composition formula gives the asserted equality.
-/
private theorem imageIdealSheaf_ker_eq_ker_comp {Yc A A' : Scheme.{u}} (e : Yc ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion e] (σ : A ⟶ A') :
    imageIdealSheaf σ (Scheme.Hom.ker e) = Scheme.Hom.ker (e ≫ σ) :=
  (Scheme.Hom.ker_comp e σ).symm

/- English proof (authored)
The image of the original embedding ideal along the ambient immersion is the kernel ideal of the composite embedding. It has the required nonvanishing by the enlarged datum. Apply pushforward functoriality of principalization along the closed immersion of positive étale coordinate codimension, with empty boundary on both ambient schemes. Identifying the image ideal with the enlarged embedding ideal gives the asserted pushforward comparison of ambient sequences.
-/
theorem isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
  have himg : imageIdealSheaf τ (Scheme.Hom.ker G.emb) = Scheme.Hom.ker (G.emb ≫ τ) :=
    imageIdealSheaf_ker_eq_ker_comp G.emb τ
  have hJ : NonzeroOnComponents (imageIdealSheaf τ (Scheme.Hom.ker G.emb)) := by
    rw [himg]; exact hker
  have key : ∀ (J : A'.IdealSheafData) (hJ' : NonzeroOnComponents J),
      J = Scheme.Hom.ker (G.emb ≫ τ) →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        (Alg k A' q J hJ' ([] : List A'.IdealSheafData) hsnc).toSequenceOfBlowups →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
    rintro J hJ' rfl h
    exact h
  exact key _ hJ himg
    (hAlg.pushforward k G.ambient A' G.ambientStruct q τ hτ c hc hcodim
      (Scheme.Hom.ker G.emb) G.nonzeroOnComponents_ker hJ G.sncEmpty hsnc)

/- English proof (authored)
Pushforward functoriality gives the comparison of the two ambient blowup sequences. The enlarged embedding is the original embedding followed by the ambient closed immersion, so this comparison gives a chart pushforward for the embedded sequences. Chart pushforward induces an isomorphism on their blowup sequences after deleting unit-center steps, which are the outputs of the two resolution rules.
-/
theorem isomorphic_embeddedResolutionRule_enlargeAmbient [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg)
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p G).Isomorphic
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc)) := by
  have P : ChartPushforward (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) :=
    @ChartPushforward.ofIsPushforwardSeq k _ _ Y _ p _ (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) τ
      (inferInstanceAs (AlgebraicGeometry.IsClosedImmersion τ)) rfl
      (isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient G Alg hAlg A' q τ hτ hker hsnc c hc hcodim)
  exact P.inducedBlowupsWithoutIso_isomorphic (hw k Y p G) (hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc))

/- English proof (authored)
Passing to an embedded blowup sequence retains the given embedding. Composing the retained old embedding with the enlargement map therefore gives the retained enlarged embedding, by the definition of enlargement.
-/
private theorem emb_comp_ambientMap_eq_enlargeAmbient_emb [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u})
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    (G.toEmbeddedBlowupSequence Alg).emb ≫
        (show (G.toEmbeddedBlowupSequence Alg).ambient ⟶
            ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambient from τ) =
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).emb := rfl

end EmbeddingDatum

end FunctorialResolution.EmbeddedResolution

end
