import Mathlib
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

/- English proof (translation)
Use `set B := f.normalizationDiagram.obj (Opposite.op V.1) with hB`. Use `set ι := f.normalizationOpenCover.f V with hι`. Use `set j := f.toNormalization with hj`. Establish `key : ∀ b : B, (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j →`. Use `letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra`.

Use the proof step `Algebra.FiniteType Γ(X, V.1) (Localization.Away b) := by`. Introduce `b hb`. Use `letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra`. Set `g : Spec (.of (Localization.Away b)) ⟶ Spec B` to `Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))`. Establish `hg : Set.range (g ≫ ι) ⊆ Set.range j`.

Introduce and unpack `_ ⟨z, rfl⟩`. Apply `hb` to reduce the goal to its premises. Establish `: g z ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b)))` using `⟨z, rfl⟩`. Rewrite `this` using `[PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]`. Conclude with `this`.

Set `h` to `IsOpenImmersion.lift j (g ≫ ι) hg`. Establish `hh : h ≫ j = g ≫ ι` using `IsOpenImmersion.lift_fac _ _ _`. Use `haveI : LocallyOfFiniteType (h ≫ j) := by rw [hh]; infer_instance`. Use `haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h j`. Establish `e : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b))) ≫ V.2.fromSpec`.

Rewrite using `[← f.toNormalization_fromNormalization, reassoc_of% hh, hι, f.ι_fromNormalization, ← Spec.map_comp_assoc]`. Use `congr 2`. Use `haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b))) ≫ V.2.fromSpec) := by`. Rewrite using `[← e]`. Use `infer_instance`.

Use `haveI := locallyOfFiniteType_of_comp (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b)))) V.2.fromSpec`. Use `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this` as an intermediate fact. Conclude with `RingHom.finiteType_algebraMap.mp this`. Establish `hcov : ∀ x : U, f x ∈ V.1 → ∃ b : B, (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j ∧ j x ∈ ι '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B))`. Introduce `x hx`.

Establish `hx' : j x ∈ Set.range ι`. Establish `h1 : j x ∈ f.fromNormalization ⁻¹ᵁ V.1` using `by show f.fromNormalization (j x) ∈ V.1`. Rewrite using `[← Scheme.Hom.comp_apply, hj, f.toNormalization_fromNormalization]`. Conclude with `hx`. Rewrite `h1` using `[f.fromNormalization_preimage V]`.

Conclude with `h1`. Take `⟨y, hy⟩` from `hx'`. Establish `hO : IsOpen (ι ⁻¹' Set.range j)` using `j.isOpenEmbedding.isOpen_range.preimage ι.continuous`. Take `⟨_, ⟨b, rfl⟩, hyb, hbO⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show y ∈ ι ⁻¹' Set.range j from ⟨x, hy.symm⟩) hO`. Conclude with `⟨b, hbO, y, hyb, hy⟩`.

Establish `hK : IsCompact (f ⁻¹' (V.1 : Set X))` using `f.isCompact_preimage V.2.isCompact`. Set `T` to `{b : B // (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j}`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun b : T => j ⁻¹' (ι '' (PrimeSpectrum.basicOpen b.1 : Set (PrimeSpectrum B)))) (fun b => (ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen b.1).2).preimage j.continuous) (by`. Introduce `x hx`. Take `⟨b, hb, hxb⟩` from `hcov x hx`.

Conclude with `Set.mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)`. Use `⟨t.image Subtype.val, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Take `⟨b', -, rfl⟩` from `Finset.mem_image.1 hb`. Conclude with `key b'.1 b'.2`.

Introduce `x hx`. Take `⟨b, hbt, hxb⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Conclude with `⟨b.1, Finset.mem_image_of_mem _ hbt, hxb⟩`.
-/
theorem normalization_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra;
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V ''
        (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  classical
  set B := f.normalizationDiagram.obj (Opposite.op V.1) with hB
  set ι := f.normalizationOpenCover.f V with hι
  set j := f.toNormalization with hj
  have key : ∀ b : B, (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j →
      letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
      Algebra.FiniteType Γ(X, V.1) (Localization.Away b) := by
    intro b hb
    letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
    let g : Spec (.of (Localization.Away b)) ⟶ Spec B :=
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
    have hg : Set.range (g ≫ ι) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      apply hb
      have : g z ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this
    let h := IsOpenImmersion.lift j (g ≫ ι) hg
    have hh : h ≫ j = g ≫ ι := IsOpenImmersion.lift_fac _ _ _
    haveI : LocallyOfFiniteType (h ≫ j) := by rw [hh]; infer_instance
    haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h j
    have e : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b))) ≫
        V.2.fromSpec := by
      rw [← f.toNormalization_fromNormalization, reassoc_of% hh, hι, f.ι_fromNormalization,
        ← Spec.map_comp_assoc]
      congr 2
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b))) ≫ V.2.fromSpec) := by
      rw [← e]; infer_instance
    haveI := locallyOfFiniteType_of_comp (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b)))) V.2.fromSpec
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
    exact RingHom.finiteType_algebraMap.mp this
  have hcov : ∀ x : U, f x ∈ V.1 → ∃ b : B,
      (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j ∧
        j x ∈ ι '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
    intro x hx
    have hx' : j x ∈ Set.range ι := by
      have h1 : j x ∈ f.fromNormalization ⁻¹ᵁ V.1 := by
        show f.fromNormalization (j x) ∈ V.1
        rw [← Scheme.Hom.comp_apply, hj, f.toNormalization_fromNormalization]
        exact hx
      rw [f.fromNormalization_preimage V] at h1
      exact h1
    obtain ⟨y, hy⟩ := hx'
    have hO : IsOpen (ι ⁻¹' Set.range j) := j.isOpenEmbedding.isOpen_range.preimage ι.continuous
    obtain ⟨_, ⟨b, rfl⟩, hyb, hbO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show y ∈ ι ⁻¹' Set.range j from ⟨x, hy.symm⟩) hO
    exact ⟨b, hbO, y, hyb, hy⟩
  have hK : IsCompact (f ⁻¹' (V.1 : Set X)) := f.isCompact_preimage V.2.isCompact
  let T := {b : B // (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun b : T => j ⁻¹' (ι '' (PrimeSpectrum.basicOpen b.1 : Set (PrimeSpectrum B))))
    (fun b => (ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen b.1).2).preimage
      j.continuous)
    (by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := hcov x hx
      exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    exact key b'.1 b'.2
  · intro x hx
    obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨b.1, Finset.mem_image_of_mem _ hbt, hxb⟩

end GlobalTheory
