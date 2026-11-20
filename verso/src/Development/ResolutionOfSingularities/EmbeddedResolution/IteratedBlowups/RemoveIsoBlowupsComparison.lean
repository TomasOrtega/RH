import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X Y : Scheme.{u}}

/- English proof (authored)
The first admissible index at or above the starting index in the second sequence is also admissible in the first. If it is within the common length, its center is nontrivial in both sequences by hypothesis. If it is at or beyond the length, it meets the stopping condition in both. Minimality in the first sequence gives the inequality.
-/
private theorem nextNontrivialIndex_le_of_center_eq_top_iff (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y)
    (hlen : s.length = t.length)
    (htriv : ∀ i, i < s.length → (s.center i = ⊤ ↔ t.center i = ⊤)) (a : ℕ) :
    s.nextNontrivialIndex a ≤ t.nextNontrivialIndex a := by
  refine s.nextNontrivialIndex_le (t.le_nextNontrivialIndex a) ?_
  rcases Nat.lt_or_ge (t.nextNontrivialIndex a) s.length with h | h
  · refine Or.inl ?_
    have hlt : t.nextNontrivialIndex a < t.length := by rw [← hlen]; exact h
    rcases t.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
    · intro hc
      exact hd ((htriv _ h).1 hc)
    · exact absurd hd (not_le.mpr hlt)
  · exact Or.inr h

/- English proof (authored)
Apply the comparison inequality in both directions. Reversing the roles of the sequences preserves equal length and exchanges the two sides of the equivalence for unit centers. The two inequalities give equality.
-/
theorem nextNontrivialIndex_congr_of_center_eq_top_iff (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y)
    (hlen : s.length = t.length)
    (htriv : ∀ i, i < s.length → (s.center i = ⊤ ↔ t.center i = ⊤)) (a : ℕ) :
    s.nextNontrivialIndex a = t.nextNontrivialIndex a := by
  refine le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff s t hlen htriv a) ?_
  refine nextNontrivialIndex_le_of_center_eq_top_iff t s hlen.symm ?_ a
  intro i hi
  have hi' : i < s.length := by rw [hlen]; exact hi
  exact (htriv i hi').symm

/- English proof (authored)
The first retained indices agree because both searches start at zero. If the current retained indices agree, the next searches start at the same successor index and again have equal results. Induction gives pointwise equality of the index functions.
-/
theorem nontrivialIndex_congr_of_center_eq_top_iff (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y)
    (hlen : s.length = t.length)
    (htriv : ∀ i, i < s.length → (s.center i = ⊤ ↔ t.center i = ⊤)) :
    s.nontrivialIndex = t.nontrivialIndex := by
  funext j
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv _

/- English proof (authored)
If the first shortened length exceeded the second, its retained index at the second shortened length would still be below the common original length. At the same position the second retained index is at least the original length, by the stopping criterion. This contradicts equality of their retained index functions.
-/
private theorem lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y)
    (hlen : s.length = t.length) (hret : s.nontrivialIndex = t.nontrivialIndex) :
    s.lengthWithoutIsoBlowups ≤ t.lengthWithoutIsoBlowups := by
  by_contra hc
  push Not at hc
  have h1 : s.nontrivialIndex t.lengthWithoutIsoBlowups < s.length := s.nontrivialIndex_lt_length hc
  have h2 : t.length ≤ t.nontrivialIndex t.lengthWithoutIsoBlowups := t.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  rw [← hret, ← hlen] at h2
  exact absurd h2 (not_le.mpr h1)

/- English proof (authored)
The two retained index functions agree because the sequences have the same length and the same trivial center positions. Shortened length comparison in both directions then gives equality.
-/
theorem lengthWithoutIsoBlowups_congr_of_center_eq_top_iff (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y)
    (hlen : s.length = t.length)
    (htriv : ∀ i, i < s.length → (s.center i = ⊤ ↔ t.center i = ⊤)) :
    s.lengthWithoutIsoBlowups = t.lengthWithoutIsoBlowups := by
  have hret : s.nontrivialIndex = t.nontrivialIndex := nontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv
  exact le_antisymm (lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq s t hlen hret)
    (lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq t s hlen.symm hret.symm)

end SequenceOfBlowups

/- English proof (authored)
Replace the source open by the forward inverse image of the target open. Taking the inverse isomorphism’s inverse image amounts to taking the inverse image along the composite of the inverse and forward maps. That composite is the identity.
-/
private theorem preimage_inv_eq {P Q : Scheme.{u}} (m : P ⟶ Q) [IsIso m] {V : Q.Opens}
    {U : P.Opens} (h : m ⁻¹ᵁ V = U) : (inv m) ⁻¹ᵁ U = V := by
  rw [← h, ← Scheme.Hom.comp_preimage, IsIso.inv_hom_id, Scheme.Hom.id_preimage]

/- English proof (authored)
Pullback of the ideal along the composite is successive pullback along the two maps. Base-changing the closed subscheme along the isomorphism identifies its pulled-back subscheme with the original one and gives an isomorphism commuting with the closed inclusions.
-/
private theorem exists_isIso_subscheme_comap_of_isIso {A B C : Scheme.{u}} (e : C ⟶ B) [IsIso e] (π : B ⟶ A)
    (D : A.IdealSheafData) :
    ∃ m : (D.comap (e ≫ π)).subscheme ⟶ (D.comap π).subscheme,
      IsIso m ∧ m ≫ (D.comap π).subschemeι = (D.comap (e ≫ π)).subschemeι ≫ e := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso e (D.comap π)

/- English proof (authored)
The ambient isomorphism induces an isomorphism of the two pulled-back closed subschemes. The support of the pulled-back center is the inverse image of the original center support, and taking complements commutes with inverse image. Because the subscheme isomorphism commutes with the inclusions, it identifies the two opens used for strict transform. Restrict the isomorphism and its inverse to those opens. They are still inverse after composing with the open inclusions, and the restricted forward map commutes with the strict-transform immersions.
-/
private theorem exists_isIso_strictTransformOpens_of_isIso {A B C : Scheme.{u}} (e : C ⟶ B) [IsIso e] (π : B ⟶ A)
    (Z D : A.IdealSheafData) :
    ∃ φ : (strictTransformOpens (e ≫ π) Z D).toScheme ⟶
        (strictTransformOpens π Z D).toScheme,
      IsIso φ ∧ φ ≫ strictTransformι π Z D
        = strictTransformι (e ≫ π) Z D ≫ e := by
  obtain ⟨μ, hμiso, hμfac⟩ := exists_isIso_subscheme_comap_of_isIso e π D
  have := hμiso
  have hbase : ∀ T : Set B, ⇑μ.base ⁻¹' (⇑(D.comap π).subschemeι.base ⁻¹' T)
      = ⇑(D.comap (e ≫ π)).subschemeι.base ⁻¹' (⇑e.base ⁻¹' T) := by
    intro T
    have h := congrArg (fun m : (D.comap (e ≫ π)).subscheme ⟶ B => ⇑m.base ⁻¹' T) hμfac
    simpa [Set.preimage_comp] using h
  have hsupp : (((Z.comap (e ≫ π)).support.compl : C.Opens) : Set C)
      = ⇑e.base ⁻¹' (((Z.comap π).support.compl : B.Opens) : Set B) := by
    have h1 : (((Z.comap π).support : TopologicalSpace.Closeds B) : Set B)
        = ⇑π.base ⁻¹' (Z.support : Set A) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    have h2 : (((Z.comap (e ≫ π)).support : TopologicalSpace.Closeds C) : Set C)
        = ⇑(e ≫ π).base ⁻¹' (Z.support : Set A) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    show (((Z.comap (e ≫ π)).support : TopologicalSpace.Closeds C) : Set C)ᶜ
        = ⇑e.base ⁻¹' ((((Z.comap π).support : TopologicalSpace.Closeds B) : Set B)ᶜ)
    rw [h1, h2, Set.preimage_compl]
    simp [Set.preimage_comp]
  have hset : ⇑μ.base ⁻¹' ((strictTransformOpens π Z D :
        ((D.comap π).subscheme).Opens) : Set ((D.comap π).subscheme))
      = ((strictTransformOpens (e ≫ π) Z D :
        ((D.comap (e ≫ π)).subscheme).Opens) : Set ((D.comap (e ≫ π)).subscheme)) := by
    rw [coe_strictTransformOpens, coe_strictTransformOpens, hbase, hsupp]
  have hopens : μ ⁻¹ᵁ (strictTransformOpens π Z D)
      = strictTransformOpens (e ≫ π) Z D := TopologicalSpace.Opens.ext hset
  have hopens2 : (inv μ) ⁻¹ᵁ (strictTransformOpens (e ≫ π) Z D)
      = strictTransformOpens π Z D := preimage_inv_eq μ hopens
  refine ⟨μ.resLE (strictTransformOpens π Z D) (strictTransformOpens (e ≫ π) Z D)
      hopens.ge, ?_, ?_⟩
  · refine ⟨(inv μ).resLE (strictTransformOpens (e ≫ π) Z D)
      (strictTransformOpens π Z D) hopens2.ge, ?_, ?_⟩
    · rw [← cancel_mono (Scheme.Opens.ι (strictTransformOpens (e ≫ π) Z D)),
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [← cancel_mono (Scheme.Opens.ι (strictTransformOpens π Z D)),
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  · rw [strictTransformι_eq_ι_comp_subschemeι, strictTransformι_eq_ι_comp_subschemeι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, hμfac, ← Category.assoc]

/- English proof (authored)
The unit center ideal has empty support, so its pullback also has empty support. The open used to define the strict transform is therefore the entire pulled-back subscheme, and its open inclusion is an isomorphism. Taking the kernel of the composite immersion gives the kernel of the pulled-back closed immersion itself, which is the pulled-back ideal.
-/
theorem strictTransform_top_eq_comap {A B : Scheme.{u}} (π : B ⟶ A) (D : A.IdealSheafData)
    [QuasiCompact (strictTransformι π ⊤ D)] :
    Blowup.strictTransform π ⊤ D = D.comap π := by
  have hs : (((⊤ : A.IdealSheafData).support : TopologicalSpace.Closeds A) : Set A) = ∅ := by
    simp
  have hsupp : ((((⊤ : A.IdealSheafData).comap π).support :
        TopologicalSpace.Closeds B) : Set B)
      = ⇑π.base ⁻¹' (((⊤ : A.IdealSheafData).support : TopologicalSpace.Closeds A) : Set A) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hc : ((((⊤ : A.IdealSheafData).comap π).support.compl : B.Opens) : Set B) = Set.univ := by
    show (((((⊤ : A.IdealSheafData).comap π).support : TopologicalSpace.Closeds B) : Set B))ᶜ
        = Set.univ
    rw [hsupp, hs]
    simp
  have hU : ((strictTransformOpens π ⊤ D : ((D.comap π).subscheme).Opens) :
      Set ((D.comap π).subscheme)) = Set.univ := by
    rw [coe_strictTransformOpens, hc, Set.preimage_univ]
  have hrange : ∀ g : (D.comap π).subscheme ⟶ (D.comap π).subscheme,
      Set.range ⇑g.base
        ⊆ Set.range ⇑(Scheme.Opens.ι (strictTransformOpens π ⊤ D)).base := by
    intro g
    rw [Scheme.Opens.range_ι, hU]
    exact Set.subset_univ _
  have : IsIso (Scheme.Opens.ι (strictTransformOpens π ⊤ D)) := by
    refine ⟨IsOpenImmersion.lift (Scheme.Opens.ι (strictTransformOpens π ⊤ D)) (𝟙 _)
      (hrange (𝟙 _)), ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [← cancel_mono (Scheme.Opens.ι (strictTransformOpens π ⊤ D)), Category.assoc,
      IsOpenImmersion.lift_fac, Category.comp_id, Category.id_comp]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/- English proof (authored)
The isomorphism between the two strict-transform opens commutes with their maps into the original source. Thus precomposing the original strict-transform immersion with that isomorphism leaves its kernel unchanged and gives the same kernel as the new immersion followed by the ambient isomorphism. Pulling this kernel back along the ambient isomorphism gives the kernel of the new immersion. These kernels are the strict-transform ideals.
-/
theorem strictTransform_isIso_comp {A B C : Scheme.{u}} [IsLocallyNoetherian B]
    [IsLocallyNoetherian C] (e : C ⟶ B) [IsIso e] (π : B ⟶ A) (Z D : A.IdealSheafData)
    (_hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Blowup.strictTransform (e ≫ π) Z D = (Blowup.strictTransform π Z D).comap e := by
  have : QuasiCompact (strictTransformι (e ≫ π) Z D) := inferInstance
  have : QuasiCompact (strictTransformι (e ≫ π) Z D ≫ e) := inferInstance
  obtain ⟨φ, hφiso, hφfac⟩ := exists_isIso_strictTransformOpens_of_isIso e π Z D
  have := hφiso
  have hker : (strictTransformι (e ≫ π) Z D ≫ e).ker
      = (strictTransformι π Z D).ker :=
    ker_eq_ker_of_isIso_comp _ _ φ hφfac
  have h2 := Blowup.comap_ker_comp_of_isOpenImmersion (strictTransformι (e ≫ π) Z D) e
  rw [strictTransform_eq_ker_strictTransformι, strictTransform_eq_ker_strictTransformι, ← h2, hker]

end FunctorialResolution.EmbeddedResolution
