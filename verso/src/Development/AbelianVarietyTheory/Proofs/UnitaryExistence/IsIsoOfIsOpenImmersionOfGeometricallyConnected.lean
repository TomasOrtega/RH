import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace OpenSubgroupScheme

variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hr : Set.range x.left ⊆ Set.range p.left`. Introduce and unpack `_ ⟨z, rfl⟩`. Establish `: z = IsLocalRing.closedPoint K` using `Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _`.

Rewrite using `[this]`. Conclude with `h`. Use `⟨Over.homMk (IsOpenImmersion.lift p.left x.left hr) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w p, ← Category.assoc, IsOpenImmersion.lift_fac]`. Conclude with `Over.w x`.

Use `ext1`. Simplify using the standard rewrite rules. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨a.left (IsLocalRing.closedPoint K), rfl⟩`.
-/
lemma mem_range_iff_factors (p : Ga ⟶ G) [IsOpenImmersion p.left] (x : 𝟙_ _ ⟶ G) :
    x.left (IsLocalRing.closedPoint K) ∈ Set.range p.left ↔ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = x := by
  constructor
  · intro h
    have hr : Set.range x.left ⊆ Set.range p.left := by
      rintro _ ⟨z, rfl⟩
      have : z = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
      rw [this]; exact h
    refine ⟨Over.homMk (IsOpenImmersion.lift p.left x.left hr) ?_, ?_⟩
    · rw [← Over.w p, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w x
    · ext1
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨a.left (IsLocalRing.closedPoint K), rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy), pointOfClosedPoint_apply G.hom y hy _⟩`.
-/
lemma exists_point [IsAlgClosed K] [LocallyOfFiniteType G.hom] (y : G.left) (hy : IsClosed {y}) :
    ∃ x : 𝟙_ _ ⟶ G, x.left (IsLocalRing.closedPoint K) = y :=
  ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
    pointOfClosedPoint_apply G.hom y hy _⟩

/- English proof (translation)
Rewrite using `[GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc, Category.comp_id, ← Category.assoc, Subsingleton.elim (x ≫ toUnit G) (𝟙 _), Category.id_comp]`.
-/
lemma comp_mulRight [GrpObj G] (x g : 𝟙_ _ ⟶ G) : x ≫ (GrpObj.mulRight g).hom = x * g := by
  rw [GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc, Category.comp_id, ← Category.assoc,
    Subsingleton.elim (x ≫ toUnit G) (𝟙 _), Category.id_comp]

/- English proof (translation)
Rewrite using `[← comp_mulRight]`. Both sides reduce to the same expression.
-/
lemma mulRight_apply [GrpObj G] (x g : 𝟙_ _ ⟶ G) :
    (GrpObj.mulRight g).hom.left (x.left (IsLocalRing.closedPoint K)) =
      (x * g).left (IsLocalRing.closedPoint K) := by
  rw [← comp_mulRight]; rfl

/- English proof (translation)
Use `LocallyOfFiniteType.jacobsonSpace G.hom` as an intermediate fact. Use `set U : Set G.left := Set.range p.left with hU`. Establish `hUo : IsOpen U` using `p.left.isOpenEmbedding.isOpen_range`. Set `V : Set G.left` to `⋃ g : {g : 𝟙_ _ ⟶ G // ¬ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = g}, (GrpObj.mulRight g.1).hom.left ⁻¹' U`. Establish `hVo : IsOpen V` using `isOpen_iUnion fun g => hUo.preimage (Scheme.Hom.continuous _)`.

Establish `hdisj : U ∩ V = ∅`. Assume the negation of the conclusion as `hne`. Take `⟨y, ⟨hyU, hyV⟩, hyc⟩` from `nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne) (hUo.inter hVo).isLocallyClosed`. Take `⟨x, rfl⟩` from `exists_point y hyc`. Take `⟨g, hg⟩` from `Set.mem_iUnion.mp hyV`.

Rewrite `hg` using `[Set.mem_preimage, mulRight_apply]`. Take `⟨a, ha⟩` from `(mem_range_iff_factors p x).mp hyU`. Take `⟨b, hb⟩` from `(mem_range_iff_factors p _).mp hg`. Use `g.2 ⟨a⁻¹ * b, ?_⟩` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, ha, hb, inv_mul_cancel_left]`.

Establish `hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint K) ∈ U` using `(mem_range_iff_factors p _).mpr ⟨1, MonObj.one_comp p⟩`. Establish `hcov : U ∪ V = Set.univ`. Assume the negation of the conclusion as `hne`. Take `⟨y, hy, hyc⟩` from `nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne) (hUo.union hVo).isClosed_compl.isLocallyClosed`. Take `⟨x, rfl⟩` from `exists_point y hyc`.

Rewrite `hy` using `[Set.mem_compl_iff, Set.mem_union, not_or]`. Use `hy.2 (Set.mem_iUnion.mpr ⟨⟨x⁻¹, ?_⟩, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩`. Use `hy.1 ((mem_range_iff_factors p x).mpr ⟨a⁻¹, ?_⟩)` and prove the remaining obligations. Rewrite using `[GrpObj.inv_comp, ha, inv_inv]`.

Rewrite using `[Set.mem_preimage, mulRight_apply, mul_inv_cancel]`. Conclude with `hone`. Establish `hc : Uᶜ = V`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `((hcov ▸ Set.mem_univ y : y ∈ U ∪ V)).resolve_left hy`. Introduce `hy hyU`. Conclude with `(hdisj ▸ ⟨hyU, hy⟩ : y ∈ (∅ : Set G.left))`. Establish `hcl : IsClopen U` using `⟨isOpen_compl_iff.mp (hc ▸ hVo), hUo⟩`.

Conclude with `hcl.eq_univ ⟨_, hone⟩`.
-/
lemma range_eq_univ [IsAlgClosed K] [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    [IsOpenImmersion p.left] [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    Set.range p.left = Set.univ := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range p.left with hU
  have hUo : IsOpen U := p.left.isOpenEmbedding.isOpen_range
  let V : Set G.left := ⋃ g : {g : 𝟙_ _ ⟶ G // ¬ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = g},
    (GrpObj.mulRight g.1).hom.left ⁻¹' U
  have hVo : IsOpen V := isOpen_iUnion fun g => hUo.preimage (Scheme.Hom.continuous _)
  have hdisj : U ∩ V = ∅ := by
    by_contra hne
    obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      (hUo.inter hVo).isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hyV
    rw [Set.mem_preimage, mulRight_apply] at hg
    obtain ⟨a, ha⟩ := (mem_range_iff_factors p x).mp hyU
    obtain ⟨b, hb⟩ := (mem_range_iff_factors p _).mp hg
    refine g.2 ⟨a⁻¹ * b, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha, hb, inv_mul_cancel_left]
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint K) ∈ U :=
    (mem_range_iff_factors p _).mpr ⟨1, MonObj.one_comp p⟩
  have hcov : U ∪ V = Set.univ := by
    by_contra hne
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      (hUo.union hVo).isClosed_compl.isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hy
    refine hy.2 (Set.mem_iUnion.mpr ⟨⟨x⁻¹, ?_⟩, ?_⟩)
    · rintro ⟨a, ha⟩
      refine hy.1 ((mem_range_iff_factors p x).mpr ⟨a⁻¹, ?_⟩)
      rw [GrpObj.inv_comp, ha, inv_inv]
    · rw [Set.mem_preimage, mulRight_apply, mul_inv_cancel]
      exact hone
  have hc : Uᶜ = V := by
    ext y
    constructor
    · intro hy
      exact ((hcov ▸ Set.mem_univ y : y ∈ U ∪ V)).resolve_left hy
    · intro hy hyU
      exact (hdisj ▸ ⟨hyU, hy⟩ : y ∈ (∅ : Set G.left))
  have hcl : IsClopen U := ⟨isOpen_compl_iff.mp (hc ▸ hVo), hUo⟩
  exact hcl.eq_univ ⟨_, hone⟩

end OpenSubgroupScheme

/- English proof (translation)
Introduce `S Ga G _ _ p _ _ _ _`. Establish `hsurj : Set.range p.left = Set.univ`. Use `Set.eq_univ_of_forall fun y => ?_` and prove the remaining obligations. Set `s : S` to `G.hom y`. Set `Ω : Type` to `AlgebraicClosure (S.residueField s)`.

Set `t : Spec (CommRingCat.of Ω) ⟶ S` to `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s`. Establish `ht : G.hom y = t (IsLocalRing.closedPoint Ω)` using `(Scheme.fromSpecResidueField_apply s _).symm`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback y _ ht`. Establish `: IsOpenImmersion ((Over.pullback t).map p).left` using `MorphismProperty.overPullbackMap _ _ ‹_›`. Establish `: LocallyOfFiniteType ((Over.pullback t).obj G).hom` using `by show LocallyOfFiniteType (pullback.snd G.hom t); infer_instance`.

Establish `: ConnectedSpace ((Over.pullback t).obj G).left` using `GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)`. Establish `h` using `OpenSubgroupScheme.range_eq_univ ((Over.pullback t).map p)`. Take `⟨w, hw⟩ : z ∈ Set.range ((Over.pullback t).map p).left` from `h ▸ Set.mem_univ _`. Use `⟨pullback.fst Ga.hom t w, ?_⟩` and prove the remaining obligations. Establish `e : ((Over.pullback t).map p).left ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left` using `pullback.lift_fst _ _ _`.

Rewrite using `[← hz, ← hw, ← Scheme.Hom.comp_apply, ← e]`. Both sides reduce to the same expression. Establish `: IsIso p.left` using `isIso_of_isOpenImmersion_of_opensRange_eq_top p.left (by ext1`. Conclude with `hsurj)`. Establish `: IsIso ((Over.forget S).map p)` using `this`.

Conclude with `isIso_of_reflects_iso p (Over.forget S)`.
-/
theorem isIso_of_isOpenImmersion_of_geometricallyConnected :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      IsOpenImmersion p.left → LocallyOfFiniteType G.hom → GeometricallyConnected G.hom → IsIso p := by
  intro S Ga G _ _ p _ _ _ _
  have hsurj : Set.range p.left = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    let s : S := G.hom y
    let Ω : Type := AlgebraicClosure (S.residueField s)
    let t : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s
    have ht : G.hom y = t (IsLocalRing.closedPoint Ω) :=
      (Scheme.fromSpecResidueField_apply s _).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ ht
    have : IsOpenImmersion ((Over.pullback t).map p).left :=
      MorphismProperty.overPullbackMap _ _ ‹_›
    have : LocallyOfFiniteType ((Over.pullback t).obj G).hom := by
      show LocallyOfFiniteType (pullback.snd G.hom t); infer_instance
    have : ConnectedSpace ((Over.pullback t).obj G).left :=
      GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
    have h := OpenSubgroupScheme.range_eq_univ ((Over.pullback t).map p)
    obtain ⟨w, hw⟩ : z ∈ Set.range ((Over.pullback t).map p).left := h ▸ Set.mem_univ _
    refine ⟨pullback.fst Ga.hom t w, ?_⟩
    have e : ((Over.pullback t).map p).left ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left :=
      pullback.lift_fst _ _ _
    rw [← hz, ← hw, ← Scheme.Hom.comp_apply, ← e]
    rfl
  have : IsIso p.left := isIso_of_isOpenImmersion_of_opensRange_eq_top p.left (by
    ext1
    exact hsurj)
  have : IsIso ((Over.forget S).map p) := this
  exact isIso_of_reflects_iso p (Over.forget S)

end GlobalTheory
