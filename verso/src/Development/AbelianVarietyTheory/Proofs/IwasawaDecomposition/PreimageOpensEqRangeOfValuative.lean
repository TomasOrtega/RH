import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
namespace GlobalTheory

/- English proof (translation)
Establish `hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU`. Set `g : F ⟶ U` to `IsOpenImmersion.lift U.ι (j ≫ π) hg`. Establish `hgfac : g ≫ U.ι = j ≫ π` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hU ⟨x, rfl⟩`. Set `j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens)` to `IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'`.

Establish `hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hcomp : j' ≫ (π ∣_ U) = g`. Rewrite using `[← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]`. Use `haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩`. Use `haveI : UniversallyClosed g := by`.

Apply `UniversallyClosed.of_valuativeCriterion` to reduce the goal to its premises. Introduce `S`. Take `⟨l, hl1, hl2⟩` from `hv S.R S.K S.i₁ (S.i₂ ≫ U.ι) (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]`.

Conclude with `⟨_, rfl⟩)`. Use the proof step `(by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])`. Establish `hl3 : l ≫ g = S.i₂`. Rewrite using `[← cancel_mono U.ι, Category.assoc, hgfac, hl2]`. Conclude with `⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩`.

Use `haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance`. Use `haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance`. Use `haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance`. Use `haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι`. Use `haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)`.

Establish `hclosed : IsClosed (Set.range j'.base)` using `j'.isClosedMap.isClosed_range`. Establish `hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩`.

Introduce and unpack `⟨x, hx⟩`. Use `⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hj'fac, hx]`. Establish `hdense : Dense (Set.range j')`. Rewrite using `[hrange]`.

Conclude with `hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap`. Establish `huniv : Set.range j' = Set.univ`. Rewrite using `[← hclosed.closure_eq]`. Conclude with `hdense.closure_eq`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι` using `by rw [Scheme.Opens.range_ι]; exact hz`. Take `⟨w, rfl⟩` from `hz'`. Take `⟨x, rfl⟩ : w ∈ Set.range j'` from `huniv ▸ Set.mem_univ w`.

Conclude with `⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `hU ⟨x, rfl⟩`.
-/
theorem preimage_opens_eq_range_of_valuative (F Z X : Scheme.{0}) (j : F ⟶ Z) (π : Z ⟶ X) (U : X.Opens)
    (hj : IsOpenImmersion j) (hd : Dense (Set.range j)) (hπ : IsSeparated π)
    (hF : TopologicalSpace.NoetherianSpace F) (hU : Set.range (j ≫ π) ⊆ (U : Set X))
    (hv : ∀ (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
      [IsFractionRing A K] (a : Sp K ⟶ F) (b : Sp A ⟶ X), Set.range b ⊆ (U : Set X) →
      a ≫ j ≫ π = spMap (algebraMap A K) ≫ b →
      ∃ l : Sp A ⟶ F, spMap (algebraMap A K) ≫ l = a ∧ l ≫ j ≫ π = b) :
    π ⁻¹' (U : Set X) = Set.range j := by
  have hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hU
  let g : F ⟶ U := IsOpenImmersion.lift U.ι (j ≫ π) hg
  have hgfac : g ≫ U.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  let j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'
  have hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : j' ≫ (π ∣_ U) = g := by
    rw [← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]
  haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : UniversallyClosed g := by
    apply UniversallyClosed.of_valuativeCriterion
    intro S
    obtain ⟨l, hl1, hl2⟩ := hv S.R S.K S.i₁ (S.i₂ ≫ U.ι)
      (by
        rintro _ ⟨x, rfl⟩
        rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      (by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])
    have hl3 : l ≫ g = S.i₂ := by
      rw [← cancel_mono U.ι, Category.assoc, hgfac, hl2]
    exact ⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩
  haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance
  haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance
  haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι
  haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)
  have hclosed : IsClosed (Set.range j'.base) := j'.isClosedMap.isClosed_range
  have hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j := by
    ext w; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj'fac, hx]
  have hdense : Dense (Set.range j') := by
    rw [hrange]; exact hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have huniv : Set.range j' = Set.univ := by
    rw [← hclosed.closure_eq]; exact hdense.closure_eq
  ext z; constructor
  · intro hz
    have hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨x, rfl⟩ : w ∈ Set.range j' := huniv ▸ Set.mem_univ w
    exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩; exact hU ⟨x, rfl⟩

end GlobalTheory
