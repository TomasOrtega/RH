import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Establish `hes : f (e s) = s`. Rewrite using `[← Scheme.Hom.comp_apply, he]`. Both sides reduce to the same expression. Establish `hrange : Set.range (f.fiberι s) = f ⁻¹' {s}` using `f.range_fiberι s`. Take `⟨y₀, hy₀⟩ : e s ∈ Set.range (f.fiberι s)` from `by rw [hrange]; exact hes`.

Establish `hpb : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s)` using `IsPullback.of_hasPullback _ _`. Establish `hft : LocallyOfFiniteType (f.fiberToSpecResidueField s)` using `MorphismProperty.of_isPullback hpb inferInstance`. Establish `hN : IsLocallyNoetherian (f.fiber s)` using `LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)`. Establish `hopen` using `GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hN y₀`. Take `⟨U, hU, hUe⟩` from `(f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hopen`.

Use `⟨⟨U, hU⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e s ∈ U`. Rewrite using `[← hy₀]`. Establish `: y₀ ∈ connectedComponent y₀` using `mem_connectedComponent`. Rewrite `this` using `[← hUe]`.

Conclude with `this`. Introduce `x hx hxs`. Take `⟨y, rfl⟩ : x ∈ Set.range (f.fiberι s)` from `by rw [hrange]; exact hxs`. Use `(GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e s _ _ _ y₀ hpb hy₀ y).mpr ?_` and prove the remaining obligations. Rewrite using `[← hUe]`.

Conclude with `hx`.
-/
theorem exists_open_inter_fiber_subset_sectionComponent (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (s : S) :
    ∃ W₁ : X.Opens, e s ∈ W₁ ∧ ∀ x : X, x ∈ W₁ → f x = s →
      x ∈ connectedComponentIn (f ⁻¹' {s}) (e s) := by
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hrange : Set.range (f.fiberι s) = f ⁻¹' {s} := f.range_fiberι s
  obtain ⟨y₀, hy₀⟩ : e s ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hes
  have hpb : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback hpb inferInstance
  have hN : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have hopen := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hN y₀
  obtain ⟨U, hU, hUe⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hopen
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · change e s ∈ U
    rw [← hy₀]
    have : y₀ ∈ connectedComponent y₀ := mem_connectedComponent
    rw [← hUe] at this
    exact this
  · intro x hx hxs
    obtain ⟨y, rfl⟩ : x ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hxs
    refine (GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e s _ _ _ y₀ hpb hy₀ y).mpr ?_
    rw [← hUe]
    exact hx

/- English proof (translation)
Introduce `X S f e hf he s`. Establish `hes : f (e s) = s`. Rewrite using `[← Scheme.Hom.comp_apply, he]`. Both sides reduce to the same expression. Take `⟨W₁, hW₁, hW₁'⟩` from `exists_open_inter_fiber_subset_sectionComponent X S f e hf he s`.

Take `⟨_, ⟨V, hV, rfl⟩, hsV, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ`. Establish `hmem : e s ∈ ((W₁ ⊓ f ⁻¹ᵁ V : X.Opens) : Set X)` using `⟨hW₁, by`. Express the relevant statement in the definitionally equal form `f (e s) ∈ (V : Set S)`. Rewrite using `[hes]`. Conclude with `hsV⟩`.

Take `⟨_, ⟨W : X.Opens, hW, rfl⟩, hsW, hle⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hmem (W₁ ⊓ f ⁻¹ᵁ V).isOpen`. Use `⟨V, W, fun x hx => (hle hx).2, hV, hW, hsW, ?_⟩` and prove the remaining obligations. Introduce `k _ p hp`. Set `e' : Spec (CommRingCat.of k) ⟶ pullback f p` to `pullback.lift (p ≫ e) (𝟙 _) (by simp [he])`. Establish `he' : e' ≫ pullback.snd f p = 𝟙 _` using `pullback.lift_snd _ _ _`.

Establish `he'' : e' ≫ pullback.fst f p = p ≫ e` using `pullback.lift_fst _ _ _`. Establish `h1` using `GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S _ _ f (pullback.snd f p) p (pullback.fst f p) e e' hf (IsPullback.of_hasPullback f p) he he' he''`. Establish `h2` using `(GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k _ (pullback.snd f p) e' inferInstance he').2`. Rewrite `h2` using `[← h1]`. Set `j : pullback (W.ι ≫ f) p ⟶ pullback f p` to `pullback.map _ _ _ _ W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)`.

Establish `hj : IsOpenImmersion j` using `inferInstance`. Establish `hjf : j ≫ pullback.fst f p = pullback.fst _ _ ≫ W.ι` using `pullback.lift_fst _ _ _`. Establish `h3` using `h2.isPreirreducible.preimage j.isOpenEmbedding`. Prove the components needed by the constructor for the conclusion. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use `symm`. Rewrite using `[Set.eq_univ_iff_forall]`. Introduce `y`. Establish `hx : f (pullback.fst f p (j y)) = s`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hp]`.

Use `congr 1`. Conclude with `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Express the relevant statement in the definitionally equal form `pullback.fst f p (j y) ∈ connectedComponentIn (f ⁻¹' {f (pullback.fst f p (j y))}) (e (f (pullback.fst f p (j y))))`. Rewrite using `[hx]`. Use `hW₁' _ ?_ hx` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, hjf, Scheme.Hom.comp_apply]`. Conclude with `(hle (pullback.fst (W.ι ≫ f) p y).2).1`.
-/
theorem exists_affine_chart_preirreducible_fiber : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  intro X S f e hf he s
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨W₁, hW₁, hW₁'⟩ := exists_open_inter_fiber_subset_sectionComponent X S f e hf he s
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hmem : e s ∈ ((W₁ ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) := ⟨hW₁, by
    change f (e s) ∈ (V : Set S)
    rw [hes]; exact hsV⟩
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hsW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hmem (W₁ ⊓ f ⁻¹ᵁ V).isOpen
  refine ⟨V, W, fun x hx => (hle hx).2, hV, hW, hsW, ?_⟩
  intro k _ p hp
  let e' : Spec (CommRingCat.of k) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'' : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  have h1 := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S _ _ f (pullback.snd f p) p (pullback.fst f p) e e' hf
    (IsPullback.of_hasPullback f p) he he' he''
  have h2 := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k _ (pullback.snd f p) e' inferInstance he').2
  rw [← h1] at h2
  let j : pullback (W.ι ≫ f) p ⟶ pullback f p :=
    pullback.map _ _ _ _ W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hj : IsOpenImmersion j := inferInstance
  have hjf : j ≫ pullback.fst f p = pullback.fst _ _ ≫ W.ι := pullback.lift_fst _ _ _
  have h3 := h2.isPreirreducible.preimage j.isOpenEmbedding
  constructor
  convert h3 using 1
  symm
  rw [Set.eq_univ_iff_forall]
  intro y
  have hx : f (pullback.fst f p (j y)) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hp]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  change pullback.fst f p (j y) ∈ connectedComponentIn (f ⁻¹' {f (pullback.fst f p (j y))})
    (e (f (pullback.fst f p (j y))))
  rw [hx]
  refine hW₁' _ ?_ hx
  rw [← Scheme.Hom.comp_apply, hjf, Scheme.Hom.comp_apply]
  exact (hle (pullback.fst (W.ι ≫ f) p y).2).1

end GlobalTheory
