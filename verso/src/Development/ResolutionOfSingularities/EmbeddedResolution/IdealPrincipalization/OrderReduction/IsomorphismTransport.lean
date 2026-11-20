import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Pull back the closed subscheme along the isomorphism. Its projection to the original closed subscheme is an isomorphism, and its projection to the new ambient scheme is that isomorphism followed by the original inclusion and the inverse ambient map. The pullback ideal is the kernel of this projection. Precomposing with an isomorphism preserves the kernel, giving the stated description.
-/
private theorem comap_eq_ker_subschemeι_comp_inv {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    I.comap f = (I.subschemeι ≫ inv f).ker := by
  have : IsIso (Limits.pullback.snd f I.subschemeι) :=
    (IsPullback.of_hasPullback f I.subschemeι).flip.isIso_fst_of_isIso
  have hw : Limits.pullback.fst f I.subschemeι
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ inv f := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  unfold AlgebraicGeometry.Scheme.IdealSheafData.comap
  rw [hw, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

/- English proof (authored)
The image ideal is the kernel of the closed-subscheme inclusion followed by the isomorphism. The formula for pullback along an isomorphism gives the same kernel when applied to the inverse isomorphism.
-/
theorem imageIdealSheaf_eq_comap_inv {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    imageIdealSheaf f J = J.comap (inv f) := by
  rw [imageIdealSheaf_eq_ker, comap_eq_ker_subschemeι_comp_inv (inv f) J, IsIso.inv_inv]

/- English proof (authored)
Image under the isomorphism is pullback along its inverse. Together with the original pullback the two operations form pullback along the identity, which fixes the ideal.
-/
theorem imageIdealSheaf_comap {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    imageIdealSheaf f (I.comap f) = I := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (authored)
Write the image as pullback along the inverse isomorphism. Pulling that ideal back along the original isomorphism gives pullback along the identity, hence the original ideal.
-/
theorem comap_imageIdealSheaf {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    (imageIdealSheaf f J).comap f = J := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (authored)
Factor the first morphism through its scheme-theoretic image. In the composite, the kernel is determined by the inclusion of this image followed by the second map. That kernel is the image ideal of the first kernel under the second map.
-/
theorem ker_comp_eq_imageIdealSheaf_ker {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) :
    (g ≫ w).ker = imageIdealSheaf w g.ker := by
  rw [imageIdealSheaf_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_comp,
    AlgebraicGeometry.Scheme.Hom.ker_comp, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

/- English proof (authored)
The inclusion of the pulled-back closed subscheme followed by the isomorphism has kernel equal to the original ideal. The universal property of a closed immersion therefore factors this composite through the original closed subscheme. The inclusion of the original subscheme followed by the inverse isomorphism likewise has kernel equal to the pulled-back ideal and factors in the opposite direction. Compose the two factorizations and check their composites with the closed inclusions. The inverse identities for the ambient isomorphism show that these composites equal the original inclusions. As the inclusions are monomorphisms, the two factorizations are inverse, and the first has the required compatibility.
-/
private theorem exists_iso_subscheme_comap_of_isIso {A B : Scheme.{u}} (w : A ⟶ B) [IsIso w]
    (I : B.IdealSheafData) :
    ∃ θ : (I.comap w).subscheme ≅ I.subscheme,
      θ.hom ≫ I.subschemeι = (I.comap w).subschemeι ≫ w := by
  have e1 : ((I.comap w).subschemeι ≫ w).ker = I := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_comap]
  have e2 : (I.subschemeι ≫ inv w).ker = I.comap w := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]
  have h1 : I.subschemeι.ker ≤ ((I.comap w).subschemeι ≫ w).ker :=
    le_of_eq (by rw [e1, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  have h2 : (I.comap w).subschemeι.ker ≤ (I.subschemeι ≫ inv w).ker :=
    le_of_eq (by rw [e2, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  refine ⟨⟨IsClosedImmersion.lift I.subschemeι ((I.comap w).subschemeι ≫ w) h1,
    IsClosedImmersion.lift (I.comap w).subschemeι (I.subschemeι ≫ inv w) h2, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono (I.comap w).subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · exact IsClosedImmersion.lift_fac ..

/- English proof (authored)
The closed subscheme of the pulled-back ideal is isomorphic to the original one, compatibly with the ambient map. Thus its inclusion followed by both maps is the original inclusion followed by the final map, precomposed with this isomorphism. Precomposition with an isomorphism fixes the kernel, which is exactly the image ideal in each case.
-/
theorem imageIdealSheaf_comp_comap_of_isIso {A B C : Scheme.{u}} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : B.IdealSheafData) :
    imageIdealSheaf (w ≫ g) (I.comap w) = imageIdealSheaf g I := by
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso w I
  rw [imageIdealSheaf_eq_ker (w ≫ g) (I.comap w), imageIdealSheaf_eq_ker g I, ← Category.assoc, ← hθ,
    Category.assoc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

/- English proof (authored)
The support of the pulled-back ideal is the inverse image of the old support. Taking complements commutes with inverse image, so the complement open is the inverse image of the old complement open.
-/
private theorem compl_support_comap {A B : Scheme.{u}} (v : A ⟶ B) (I : B.IdealSheafData) :
    (I.comap v).support.compl = (TopologicalSpace.Opens.map v.base).obj I.support.compl := by
  ext x
  simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]

/- English proof (authored)
A point maps into the chosen open under the composite precisely when its first image lies in the inverse image under the second map. Thus the two open sets have the same points.
-/
private theorem opens_map_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens) :
    (TopologicalSpace.Opens.map (f ≫ g).base).obj U
      = (TopologicalSpace.Opens.map f.base).obj ((TopologicalSpace.Opens.map g.base).obj U) := by
  ext x
  simp

/- English proof (authored)
The inverse image of any open under the identity has exactly its original points.
-/
private theorem opens_map_id {B : Scheme.{u}} (W : B.Opens) :
    (TopologicalSpace.Opens.map (𝟙 B : B ⟶ B).base).obj W = W := by
  ext x
  exact Iff.rfl

/- English proof (authored)
The isomorphism carries the inverse image open into the given open. The inverse carries the given open into its inverse image because the two ambient maps are inverse. Restrict both maps to these opens. Their composites become the identity after composing with the respective open inclusions. The inclusions are monomorphisms, so the restricted morphisms are inverse. The restriction identity for the forward map gives the required compatibility.
-/
private theorem exists_iso_opens_preimage {A B : Scheme.{u}} (θ : A ≅ B) (V' : A.Opens) (V : B.Opens)
    (hVV' : V' = (TopologicalSpace.Opens.map θ.hom.base).obj V) :
    ∃ c : (↑V' : Scheme.{u}) ≅ (↑V : Scheme.{u}), c.hom ≫ V.ι = V'.ι ≫ θ.hom := by
  have hcomp : (TopologicalSpace.Opens.map θ.inv.base).obj V'
      = (TopologicalSpace.Opens.map (θ.inv ≫ θ.hom).base).obj V := by
    rw [hVV', opens_map_comp]
  have hle : V ≤ (TopologicalSpace.Opens.map θ.inv.base).obj V' :=
    le_of_eq (by rw [hcomp, Iso.inv_hom_id, opens_map_id])
  refine ⟨⟨Scheme.Hom.resLE θ.hom V V' (le_of_eq hVV'),
    Scheme.Hom.resLE θ.inv V' V hle, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono V'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · exact Scheme.Hom.resLE_comp_ι ..

/- English proof (authored)
The second morphism is obtained by precomposing the first with an isomorphism. Precomposition with an isomorphism leaves the kernel unchanged.
-/
private theorem ker_eq_of_iso_comp {P Q T : Scheme.{u}} (c : Q ≅ P) (h₁ : P ⟶ T) (h₂ : Q ⟶ T)
    (hc : c.hom ≫ h₁ = h₂) : h₁.ker = h₂.ker := by
  rw [← hc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

/- English proof (authored)
Write the image ideals along the ambient isomorphism as pullbacks along its inverse. Commutativity of the square then identifies their pullbacks to the second blowup scheme with the original pulled-back ideals transported by the upstairs isomorphism. In particular the two pulled-back closed subschemes are isomorphic. This isomorphism identifies their open parts off the pulled-back centers, since the complement of support commutes with pullback. The strict transform is the kernel of the map from this open part to the ambient blowup scheme. The two maps agree after transport by the isomorphisms, and precomposing by the isomorphism of opens preserves the kernel. The kernel on the second blowup scheme is therefore the image of the original strict-transform ideal.
-/
theorem imageIdealSheaf_strictTransform_of_comm_sq {X X₁ Y Y₁ : Scheme.{u}}
    (φ : X₁ ⟶ X) (ψ : Y₁ ⟶ Y) (u : X ⟶ Y) (u₁ : X₁ ⟶ Y₁) [IsIso u] [IsIso u₁]
    (hsq : u₁ ≫ ψ = φ ≫ u) (Z D : X.IdealSheafData) :
    imageIdealSheaf u₁ (Blowup.strictTransform φ Z D)
      = Blowup.strictTransform ψ (imageIdealSheaf u Z) (imageIdealSheaf u D) := by
  have hψ : ψ = inv u₁ ≫ φ ≫ u := by
    rw [← hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hmaps : ψ ≫ inv u = inv u₁ ≫ φ := by
    rw [hψ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcm : ∀ I : X.IdealSheafData,
      (imageIdealSheaf u I).comap ψ = (I.comap φ).comap (inv u₁) := by
    intro I
    rw [imageIdealSheaf_eq_comap_inv,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hmaps]
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso (inv u₁) (D.comap φ)
  have hVV' : (TopologicalSpace.Opens.map ((D.comap φ).comap (inv u₁)).subschemeι.base).obj
        ((Z.comap φ).comap (inv u₁)).support.compl
      = (TopologicalSpace.Opens.map θ.hom.base).obj
        ((TopologicalSpace.Opens.map (D.comap φ).subschemeι.base).obj
          (Z.comap φ).support.compl) := by
    rw [compl_support_comap, ← opens_map_comp, ← opens_map_comp, hθ]
  obtain ⟨c, hc⟩ := exists_iso_opens_preimage θ _ _ hVV'
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq,
    hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker]
  refine ker_eq_of_iso_comp c _ _ ?_
  simp only [Category.assoc]
  rw [← Category.assoc c.hom, hc, Category.assoc, reassoc_of% hθ]
  simp

namespace IsPushforwardBlowupSeq

/- English proof (authored)
Compose each closed immersion from the source sequence with the corresponding stage isomorphism of ambient sequences. The sequences have the same length, and these composites are closed immersions. The initial identification and transition identities hold by compatibility of the ambient isomorphisms with the sequence maps. Taking image ideals along the stage isomorphisms carries the old ambient centers to the new ones, so the image-of-center condition persists. It also carries the old strict-transform identity for the immersion kernels to the corresponding new identity, since strict transforms commute with the isomorphisms by their commutative transition squares. These are the required pushforward data.
-/
theorem of_isomorphic {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  obtain ⟨hlen2, e, he0, hestep, hecent⟩ := he
  have hestep' : ∀ (i : ℕ) (hp : i + 1 ≤ B.length) (hq : i ≤ B.length),
      (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hq).hom :=
    fun i hp _ => hestep i hp
  have hecent' : ∀ (i : ℕ) (hp : i < B.length) (hq : i ≤ B.length),
      (B'.center i).comap (e i hq).hom = B.center i := fun i hp _ => hecent i hp
  refine ⟨by omega, fun i hi => σ i hi ≫ (e i (by omega)).hom, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hci i hi
    infer_instance
  · have hgoal : (σ 0 (Nat.zero_le _) ≫ (e 0 (Nat.zero_le _)).hom) ≫ B'.isoZero.hom
        = BS.isoZero.hom ≫ j := by
      rw [Category.assoc, he0, h0]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom) ≫ B'.transitionMapSucc i
        = BS.transitionMapSucc i ≫ (σ i hi.le ≫ (e i hiB.le).hom) := by
      rw [Category.assoc, hestep' i hiB hiB.le, ← Category.assoc, hstep i hi, Category.assoc]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : imageIdealSheaf (σ i hi.le ≫ (e i hiB.le).hom) (BS.center i) = B'.center i := by
      rw [imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le,
        imageIdealSheaf_comap]
    exact hgoal.symm
  · intro i hi
    have hiB : i < B.length := by omega
    have hcen : imageIdealSheaf (e i hiB.le).hom (B.center i) = B'.center i := by
      rw [← hecent' i hiB hiB.le, imageIdealSheaf_comap]
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom).ker
        = Blowup.strictTransform (B'.transitionMapSucc i) (B'.center i)
            ((σ i hi.le ≫ (e i hiB.le).hom).ker) := by
      rw [ker_comp_eq_imageIdealSheaf_ker, hker i hi,
        imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i)
          (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i)
          ((σ i hi.le).ker),
        hcen, ker_comp_eq_imageIdealSheaf_ker]
    exact hgoal

/- English proof (authored)
The stage maps of the strict pullback along the source isomorphism are isomorphisms. At stage zero this follows from the base identifications, and at a successor it follows from the pullback square and the preceding isomorphism. Precompose the old closed immersions into the ambient sequence with these stage maps. This preserves closed immersions, and compatibility of the initial maps and transition squares gives the required commutativity. Each new source center is the pullback of the old source center, so their images in the ambient scheme agree. Precomposing with stage isomorphisms leaves the immersion kernels unchanged, preserving the strict-transform identity. The common lengths yield the claimed pushforward relation.
-/
theorem isIso_comp {S' S X : Scheme.{u}} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by
  obtain ⟨hlen2, τ, hτ0, hτsq, hτcent⟩ := hpb
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  have hτ0' : ∀ hp : (0 : ℕ) ≤ BS'.length,
      τ 0 hp ≫ BS.isoZero.hom = BS'.isoZero.hom ≫ e := fun _ => hτ0
  have hiso : ∀ (i : ℕ) (hi : i ≤ BS'.length), IsIso (τ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hzz : τ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv := by
          rw [← Category.assoc, ← hτ0' hi]
          simp
        rw [hzz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < BS'.length := by omega
        have := ih (by omega)
        exact (hτsq n hn).isIso_fst_of_isIso
  refine ⟨by omega, fun i hi => τ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    have := hci i (by omega)
    infer_instance
  · have hgoal : (τ 0 (Nat.zero_le _) ≫ σ 0 (Nat.zero_le _)) ≫ B.isoZero.hom
        = BS'.isoZero.hom ≫ j' := by
      rw [hj, Category.assoc, h0, ← Category.assoc, hτ0, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i
        = BS'.transitionMapSucc i ≫ (τ i hi.le ≫ σ i hiS.le) := by
      rw [Category.assoc, hstep i hiS, ← Category.assoc, (hτsq i hi).w, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso i hi.le
    have hgoal : imageIdealSheaf (τ i hi.le ≫ σ i hiS.le) (BS'.center i) = B.center i := by
      rw [hτcent i hi, hcent i hiS]
      exact imageIdealSheaf_comp_comap_of_isIso (τ i hi.le) (σ i hiS.le) (BS.center i)
    exact hgoal.symm
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso (i + 1) hi
    have := hiso i hi.le
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS).ker
        = Blowup.strictTransform (B.transitionMapSucc i) (B.center i) ((τ i hi.le ≫ σ i hiS.le).ker) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso,
        AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
      exact hker i hiS
    exact hgoal

/- English proof (authored)
The only stage of either sequence is stage zero. Use the initial isomorphism from the source stage to its base, the given closed immersion, and the inverse initial isomorphism on the target to form the stage immersion. It is a closed immersion and commutes with the two initial identifications. There are no successor stages or centers, so all step conditions are vacuous.
-/
theorem of_length_eq_zero {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := fun i hi => by omega
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
