import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.CoproductBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FunctorialResolution.EmbeddedResolution

private def boolFamily (X₁ X₂ : Scheme.{u}) : ULift.{u} Bool → Scheme.{u} :=
  fun i => cond i.down X₁ X₂

private def boolFamilyMap {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    ∀ i, boolFamily X₁ X₂ i ⟶ boolFamily Y₁ Y₂ i
  | ⟨true⟩ => f₁
  | ⟨false⟩ => f₂

private def boolFamilyDesc {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    ∀ i, boolFamily X₁ X₂ i ⟶ Y
  | ⟨true⟩ => f₁
  | ⟨false⟩ => f₂

private noncomputable def sigmaBoolFamilyInl (X₁ X₂ : Scheme.{u}) : X₁ ⟶ ∐ boolFamily X₁ X₂ :=
  Limits.Sigma.ι (boolFamily X₁ X₂) ⟨true⟩

private noncomputable def sigmaBoolFamilyInr (X₁ X₂ : Scheme.{u}) : X₂ ⟶ ∐ boolFamily X₁ X₂ :=
  Limits.Sigma.ι (boolFamily X₁ X₂) ⟨false⟩

/- English proof (authored)
By the defining property of the coproduct map, its restriction to the first summand is f₁. Composing with the first inclusion takes this restriction.
-/
private theorem pairInl_comp_desc {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    sigmaBoolFamilyInl X₁ X₂ ≫ Limits.Sigma.desc (boolFamilyDesc f₁ f₂) = f₁ :=
  Limits.Sigma.ι_desc (boolFamilyDesc f₁ f₂) ⟨true⟩

/- English proof (authored)
The coproduct map is induced by its two stated component maps. Restricting it along the second inclusion gives f₂.
-/
private theorem pairInr_comp_desc {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    sigmaBoolFamilyInr X₁ X₂ ≫ Limits.Sigma.desc (boolFamilyDesc f₁ f₂) = f₂ :=
  Limits.Sigma.ι_desc (boolFamilyDesc f₁ f₂) ⟨false⟩

/- English proof (authored)
The map between the two coproducts is induced by applying the component map and then including its target summand. On the first component this is a₁ followed by the first inclusion.
-/
private theorem pairInl_comp_map {X₁ X₂ P₁ P₂ : Scheme.{u}} (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) :
    sigmaBoolFamilyInl P₁ P₂ ≫ Limits.Sigma.map (boolFamilyMap a₁ a₂) = a₁ ≫ sigmaBoolFamilyInl X₁ X₂ :=
  Limits.Sigma.ι_map (boolFamilyMap a₁ a₂) ⟨true⟩

/- English proof (authored)
Restrict the coproduct map to the second summand. By construction that restriction is a₂ followed by the second inclusion of the target coproduct.
-/
private theorem pairInr_comp_map {X₁ X₂ P₁ P₂ : Scheme.{u}} (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) :
    sigmaBoolFamilyInr P₁ P₂ ≫ Limits.Sigma.map (boolFamilyMap a₁ a₂) = a₂ ≫ sigmaBoolFamilyInr X₁ X₂ :=
  Limits.Sigma.ι_map (boolFamilyMap a₁ a₂) ⟨false⟩

/- English proof (authored)
The universal property of the coproduct determines any map out of it from its restrictions to the two summands. The restrictions of f and g agree on both, so f and g are equal.
-/
private theorem sigmaPair_hom_ext {X₁ X₂ Z : Scheme.{u}} (f g : (∐ boolFamily X₁ X₂) ⟶ Z)
    (ht : sigmaBoolFamilyInl X₁ X₂ ≫ f = sigmaBoolFamilyInl X₁ X₂ ≫ g)
    (hf : sigmaBoolFamilyInr X₁ X₂ ≫ f = sigmaBoolFamilyInr X₁ X₂ ≫ g) : f = g := by
  apply Limits.Sigma.hom_ext
  rintro ⟨(_ | _)⟩
  · exact hf
  · exact ht

private noncomputable def coprodIsoSigmaBoolFamily (X₁ X₂ : Scheme.{u}) : (X₁ ⨿ X₂) ≅ ∐ boolFamily X₁ X₂ where
  hom := coprod.desc (sigmaBoolFamilyInl X₁ X₂) (sigmaBoolFamilyInr X₁ X₂)
  inv := Limits.Sigma.desc (boolFamilyDesc (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, Category.comp_id]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, Category.comp_id]
  inv_hom_id := by
    apply sigmaPair_hom_ext
    · rw [← Category.assoc, pairInl_comp_desc, coprod.inl_desc, Category.comp_id]
    · rw [← Category.assoc, pairInr_comp_desc, coprod.inr_desc, Category.comp_id]

/- English proof (authored)
The comparison isomorphism is constructed with forward map induced by the two inclusions into the indexed coproduct. This is the stated binary coproduct map.
-/
private theorem pairCoprodIso_hom (X₁ X₂ : Scheme.{u}) :
    (coprodIsoSigmaBoolFamily X₁ X₂).hom = coprod.desc (sigmaBoolFamilyInl X₁ X₂) (sigmaBoolFamilyInr X₁ X₂) := rfl

private noncomputable def isoCoprodInitial (P : Scheme.{u}) : P ≅ P ⨿ (⊥_ Scheme.{u}) where
  hom := coprod.inl
  inv := coprod.desc (𝟙 P) (initial.to P)
  hom_inv_id := coprod.inl_desc (𝟙 P) (initial.to P)
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, Category.id_comp, Category.comp_id]
    · exact initial.hom_ext _ _

/- English proof (authored)
The isomorphism from P to the coproduct of P and the initial scheme is built with forward map the inclusion of the first summand. Its inverse is induced by the identity of P and the unique map from the initial scheme.
-/
private theorem coprodInitialIsoRight_hom (P : Scheme.{u}) :
    (isoCoprodInitial P).hom = (coprod.inl : P ⟶ P ⨿ (⊥_ Scheme.{u})) := rfl

private noncomputable def isoInitialCoprod (P : Scheme.{u}) : P ≅ (⊥_ Scheme.{u}) ⨿ P where
  hom := coprod.inr
  inv := coprod.desc (initial.to P) (𝟙 P)
  hom_inv_id := coprod.inr_desc (initial.to P) (𝟙 P)
  inv_hom_id := by
    apply coprod.hom_ext
    · exact initial.hom_ext _ _
    · rw [← Category.assoc, coprod.inr_desc, Category.id_comp, Category.comp_id]

/- English proof (authored)
The isomorphism from P to the coproduct of the initial scheme and P is built with forward map the inclusion of the second summand. Its inverse is induced by the unique map from the initial scheme and the identity of P.
-/
private theorem coprodInitialIsoLeft_hom (P : Scheme.{u}) :
    (isoInitialCoprod P).hom = (coprod.inr : P ⟶ (⊥_ Scheme.{u}) ⨿ P) := rfl

private noncomputable def isInitialOfIsEmptyScheme {X : Scheme.{u}} (h : IsEmpty X) : IsInitial X := by
  haveI := h
  exact isInitialOfIsEmpty

/- English proof (authored)
Identify X′ with X and P′ with P through the given isomorphisms. The compatibility equations identify the new arrows with the old arrows transported through those isomorphisms. A cone on the new square therefore corresponds to a cone on the old pullback square, with the same unique factorization after transport. This gives the pullback property for the new square.
-/
private theorem isPullback_of_isPullback_of_iso {P X Y Z P' X' : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst' : P' ⟶ X'} {snd' : P' ⟶ Y} {f' : X' ⟶ Z}
    (h : IsPullback fst snd f g) (eP : P' ≅ P) (eX : X' ≅ X)
    (h1 : fst' ≫ eX.hom = eP.hom ≫ fst) (h2 : eX.hom ≫ f = f')
    (h3 : eP.hom ≫ snd = snd') : IsPullback fst' snd' f' g := by
  have sq2 : CommSq eX.inv f f' (𝟙 Z) := by
    refine ⟨?_⟩
    rw [← h2, Iso.inv_hom_id_assoc, Category.comp_id]
  have hX : IsPullback eX.inv f f' (𝟙 Z) := IsPullback.of_horiz_isIso sq2
  have step1 := h.paste_horiz hX
  have sq1 : CommSq eP.hom (eP.hom ≫ snd) snd (𝟙 Y) := by
    refine ⟨?_⟩
    rw [Category.comp_id]
  have hP : IsPullback eP.hom (eP.hom ≫ snd) snd (𝟙 Y) := IsPullback.of_horiz_isIso sq1
  have step2 := hP.paste_horiz step1
  have hfst : fst' = eP.hom ≫ fst ≫ eX.inv := by
    rw [← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfst, ← h3]
  simpa using step2

/- English proof (authored)
Index the two given pullback squares by the two-element set. The finite coproduct pullback result gives the square with indexed coproducts. Identify each indexed coproduct with the binary coproduct by matching the two inclusions. Checking on both summands identifies each arrow with the prescribed binary coproduct map. Transport the pullback property through these isomorphisms.
-/
theorem isPullback_coprodMap_coprodDesc {X₁ X₂ P₁ P₂ Y Y' : Scheme.{u}}
    (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) (b₁ : P₁ ⟶ Y') (b₂ : P₂ ⟶ Y')
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (u : Y' ⟶ Y)
    (h₁ : IsPullback a₁ b₁ f₁ u) (h₂ : IsPullback a₂ b₂ f₂ u) :
    IsPullback (coprod.map a₁ a₂) (coprod.desc b₁ b₂) (coprod.desc f₁ f₂) u := by
  have hsq : ∀ i : ULift.{u} Bool,
      IsPullback (boolFamilyMap a₁ a₂ i) (boolFamilyDesc b₁ b₂ i) (boolFamilyDesc f₁ f₂ i) u := by
    rintro ⟨(_ | _)⟩
    · exact h₂
    · exact h₁
  have key := isPullback_sigmaMap_sigmaDesc u (boolFamily X₁ X₂) (boolFamily P₁ P₂)
      (boolFamilyMap a₁ a₂) (boolFamilyDesc b₁ b₂) (boolFamilyDesc f₁ f₂) hsq
  have E1 : coprod.map a₁ a₂ ≫ (coprodIsoSigmaBoolFamily X₁ X₂).hom
      = (coprodIsoSigmaBoolFamily P₁ P₂).hom ≫ Limits.Sigma.map (boolFamilyMap a₁ a₂) := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, pairInl_comp_map]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, pairInr_comp_map]
  have E2 : (coprodIsoSigmaBoolFamily X₁ X₂).hom ≫ Limits.Sigma.desc (boolFamilyDesc f₁ f₂)
      = coprod.desc f₁ f₂ := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, coprod.inr_desc]
  have E3 : (coprodIsoSigmaBoolFamily P₁ P₂).hom ≫ Limits.Sigma.desc (boolFamilyDesc b₁ b₂)
      = coprod.desc b₁ b₂ := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, coprod.inr_desc]
  exact isPullback_of_isPullback_of_iso key (coprodIsoSigmaBoolFamily P₁ P₂) (coprodIsoSigmaBoolFamily X₁ X₂) E1 E2 E3

/- English proof (authored)
The maps from the initial scheme form a commuting square because maps from an initial object are unique. Any competing cone has empty underlying space by hypothesis, so its vertex is itself initial in schemes. Thus it has a unique map to the initial scheme, and its composites with the two projections are the original cone maps by uniqueness. This is the pullback universal property.
-/
theorem isPullback_initial_of_isEmpty {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (u : Y' ⟶ Y)
    (h : ∀ (P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y'), a ≫ f = b ≫ u → IsEmpty P) :
    IsPullback (initial.to X) (initial.to Y') f u := by
  have hw : CommSq (initial.to X) (initial.to Y') f u := ⟨initial.hom_ext _ _⟩
  refine IsPullback.of_isLimit' hw (PullbackCone.isLimitAux' _ (fun s => ?_))
  have hinit : IsInitial s.pt := isInitialOfIsEmptyScheme (h s.pt s.fst s.snd s.condition)
  refine ⟨hinit.to _, hinit.hom_ext _ _, hinit.hom_ext _ _, ?_⟩
  intro m _ _
  exact hinit.hom_ext _ _

/- English proof (authored)
The pullback of the map from F is the initial scheme by the empty-cone criterion. Combine this square with the given pullback square for X using the binary coproduct result. The resulting pullback vertex is the coproduct of P with the initial scheme, canonically isomorphic to P by the first inclusion. Transporting the square through this isomorphism gives the desired maps.
-/
theorem isPullback_comp_inl_coprodDesc {P X Y Y' F : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y') (q : X ⟶ Y) (u : Y' ⟶ Y) (r : F ⟶ Y)
    (hsq : IsPullback a b q u)
    (hF : ∀ (Q : Scheme.{u}) (c : Q ⟶ F) (d : Q ⟶ Y'), c ≫ r = d ≫ u → IsEmpty Q) :
    IsPullback (a ≫ coprod.inl) b (coprod.desc q r) u := by
  have hFpb : IsPullback (initial.to F) (initial.to Y') r u :=
    isPullback_initial_of_isEmpty r u hF
  have key := isPullback_coprodMap_coprodDesc a (initial.to F) b (initial.to Y') q r u hsq hFpb
  have E1 : (a ≫ coprod.inl) ≫ (Iso.refl (X ⨿ F)).hom
      = (isoCoprodInitial P).hom ≫ coprod.map a (initial.to F) := by
    rw [Iso.refl_hom, Category.comp_id, coprodInitialIsoRight_hom, coprod.inl_map]
  have E2 : (Iso.refl (X ⨿ F)).hom ≫ coprod.desc q r = coprod.desc q r := by
    rw [Iso.refl_hom, Category.id_comp]
  have E3 : (isoCoprodInitial P).hom ≫ coprod.desc b (initial.to Y') = b := by
    rw [coprodInitialIsoRight_hom, coprod.inl_desc]
  exact isPullback_of_isPullback_of_iso key (isoCoprodInitial P) (Iso.refl (X ⨿ F)) E1 E2 E3

end FunctorialResolution.EmbeddedResolution
