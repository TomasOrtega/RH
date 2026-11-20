import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

/- English proof (translation)
Take `⟨i, y, rfl⟩` from `X.affineCover.exists_eq x`. Establish `hemb` using `(X.affineCover.f i).isOpenEmbedding`. Rewrite using `[← Set.image_singleton, ← hemb.isOpen_iff_image_isOpen]`. Establish `hN : IsLocallyNoetherian (X.affineCover.X i)` using `isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)`. Establish `hA : IsAffine (X.affineCover.X i)` using `inferInstance`.

Establish `: IsNoetherian (X.affineCover.X i)` using `{}`. Establish `hcl : IsClosed ({y} : Set (X.affineCover.X i))`. Use `hx.preimage hemb.continuous` as an intermediate fact. Rewrite `this` using `[← Set.image_singleton, Set.preimage_image_eq _ hemb.injective]`. Then use the resulting hypothesis. Establish `hgen : ∀ z, z ⤳ y → z = y` using `fun z hz => hemb.injective (h _ (hz.map hemb.continuous))`.

Use `clear hx h hemb`. Generalize the expression as in `X.affineCover.X i = Y at *`. Establish `hfin` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)`. Establish `hc : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents Y | y ∉ Z}, Z)` using `(hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1`. Use `hc.isOpen_compl using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `z`. Simplify using `only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl Z hZ hz`. Conclude with `hZ.2 hz`.

Introduce `H`. Establish `hm` using `irreducibleComponent_mem_irreducibleComponents z`. Establish `hy : y ∈ irreducibleComponent z`. Assume the negation of the conclusion as `hy`. Conclude with `H _ ⟨hm, hy⟩ mem_irreducibleComponent`.

Establish `hg` using `(isIrreducible_irreducibleComponent (x := z)).isGenericPoint_genericPoint isClosed_irreducibleComponent`. Establish `e` using `hgen _ (hg.specializes hy)`. Rewrite `hg` using `[e]`. Establish `: z ∈ closure {y}`. Rewrite using `[hg.def]`.

Conclude with `mem_irreducibleComponent`. Rewrite `this` using `[hcl.closure_eq]`. Then use the resulting hypothesis.
-/
theorem isOpen_singleton_of_isClosed_of_generization {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → y = x) : IsOpen ({x} : Set X) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have hemb := (X.affineCover.f i).isOpenEmbedding
  rw [← Set.image_singleton, ← hemb.isOpen_iff_image_isOpen]
  have hN : IsLocallyNoetherian (X.affineCover.X i) := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
  have hA : IsAffine (X.affineCover.X i) := inferInstance
  have : IsNoetherian (X.affineCover.X i) := {}
  have hcl : IsClosed ({y} : Set (X.affineCover.X i)) := by
    have := hx.preimage hemb.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ hemb.injective] at this
  have hgen : ∀ z, z ⤳ y → z = y := fun z hz => hemb.injective (h _ (hz.map hemb.continuous))
  clear hx h hemb
  generalize X.affineCover.X i = Y at *
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hc : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents Y | y ∉ Z}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  convert hc.isOpen_compl using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro rfl Z hZ hz
    exact hZ.2 hz
  · intro H
    have hm := irreducibleComponent_mem_irreducibleComponents z
    have hy : y ∈ irreducibleComponent z := by
      by_contra hy
      exact H _ ⟨hm, hy⟩ mem_irreducibleComponent
    have hg := (isIrreducible_irreducibleComponent (x := z)).isGenericPoint_genericPoint
      isClosed_irreducibleComponent
    have e := hgen _ (hg.specializes hy)
    rw [e] at hg
    have : z ∈ closure {y} := by
      rw [hg.def]; exact mem_irreducibleComponent
    rwa [hcl.closure_eq] at this

/- English proof (translation)
Rewrite using `[Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]`. Establish `: LocallyOfFiniteType (f.fiberToSpecResidueField (f x))` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))`. Establish `: IsLocallyNoetherian (f.fiber (f x))` using `LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))`. Establish `hemb` using `(f.fiberι (f x)).isEmbedding`. Establish `hx' : f.fiberι (f x) (f.asFiber x) = x` using `by simp`.

Apply `isOpen_singleton_of_isClosed_of_generization` to reduce the goal to its premises. Use `hx.preimage hemb.continuous` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Conclude with `⟨fun hz => by rw [hz]; exact hx', fun hz => hemb.injective (hz.trans hx'.symm)⟩`.

Introduce `y hy`. Apply `hemb.injective` to reduce the goal to its premises. Rewrite using `[hx']`. Apply `h` to reduce the goal to its premises. Use `hy.map hemb.continuous` as an intermediate fact.

Rewrite `this` using `[hx']`. Then use the resulting hypothesis. Establish `: f.fiberι (f x) y ∈ f ⁻¹' {f x}`. Rewrite using `[← f.range_fiberι]`. Conclude with `⟨y, rfl⟩`. Conclude with `this`.
-/
theorem quasiFiniteAt_of_isClosed_of_generization {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → f y = f x → y = x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hemb := (f.fiberι (f x)).isEmbedding
  have hx' : f.fiberι (f x) (f.asFiber x) = x := by simp
  apply isOpen_singleton_of_isClosed_of_generization
  · have := hx.preimage hemb.continuous
    convert this using 1
    ext z
    exact ⟨fun hz => by rw [hz]; exact hx', fun hz => hemb.injective (hz.trans hx'.symm)⟩
  · intro y hy
    apply hemb.injective
    rw [hx']
    apply h
    · have := hy.map hemb.continuous
      rwa [hx'] at this
    · have : f.fiberι (f x) y ∈ f ⁻¹' {f x} := by
        rw [← f.range_fiberι]; exact ⟨y, rfl⟩
      exact this

/- English proof (translation)
Use `(h.antisymm ?_).eq` and prove the remaining obligations. Rewrite using `[specializes_iff_forall_open]`. Introduce `V hV hy`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hyU : y ∈ U` using `h.mem_open U.2 hxU`.

Take `⟨s, hs, hys⟩` from `IsAffineOpen.exists_basicOpen_le hU (V := ⟨V, hV⟩) ⟨y, hy⟩ hyU`. Conclude with `hs (H U hxU s hys)`.
-/
theorem eq_of_specializes_of_basicOpen {X : Scheme.{0}} {y x : X} (h : y ⤳ x)
    (H : ∀ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)), y ∈ X.basicOpen s → x ∈ X.basicOpen s) : y = x := by
  refine (h.antisymm ?_).eq
  rw [specializes_iff_forall_open]
  intro V hV hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  obtain ⟨s, hs, hys⟩ := IsAffineOpen.exists_basicOpen_le hU (V := ⟨V, hV⟩) ⟨y, hy⟩ hyU
  exact hs (H U hxU s hys)

/- English proof (translation)
Introduce `C w W hw u hcl hco`. Use `C.proper` as an intermediate fact. Establish `hlft : LocallyOfFiniteType C.GG.hom` using `inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom))`. Unfold `Core.Coord at hco`. Express the relevant statement in the definitionally equal form `IsLocalRing.maximalIdeal (C.GG.left.presheaf.stalk w) = _ at hco`.

Use `set f := AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i)) with hf`. Establish `hover : f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z) = W.ι ≫ C.GG.hom` using `AffineSpace.homOfVector_over _ _`. Establish `: LocallyOfFiniteType (f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z))`. Rewrite using `[hover]`. Use `infer_instance`.

Establish `: LocallyOfFiniteType f` using `locallyOfFiniteType_of_comp f (𝔸(Fin C.g; C.Z) ↘ C.Z)`. Establish `hemb` using `W.ι.isOpenEmbedding`. Apply `quasiFiniteAt_of_isClosed_of_generization` to reduce the goal to its premises. Use `hcl.preimage hemb.continuous` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `z`. Conclude with `Subtype.ext_iff`. Introduce `y hy hfy`. Establish `hy' : y.1 ⤳ w` using `hy.map hemb.continuous`. Establish `hg : C.GG.hom y.1 = C.GG.hom w`.

Establish `e : ∀ t : W.toScheme, C.GG.hom t.1 = (𝔸(Fin C.g; C.Z) ↘ C.Z) (f t)`. Introduce `t`. Rewrite using `[← Scheme.Hom.comp_apply, hover]`. Both sides reduce to the same expression. Rewrite using `[e y, hfy, ← e ⟨w, hw⟩]`.

Apply `Subtype.ext` to reduce the goal to its premises. Set `P : Ideal (C.G.toScheme.presheaf.stalk w)` to `(IsLocalRing.maximalIdeal _).comap (C.G.toScheme.presheaf.stalkSpecializes hy').hom`. Establish `hP : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)), (C.G.toScheme.presheaf.germ U w hU).hom s ∈ P ↔ y.1 ∉ C.G.toScheme.basicOpen s`. Introduce `U hU s`. Rewrite using `[C.G.toScheme.mem_basicOpen s y.1 (hy'.mem_open U.2 hU), Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]`.

Establish `hm : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)), (C.G.toScheme.presheaf.germ U w hU).hom s ∈ IsLocalRing.maximalIdeal _ ↔ w ∉ C.G.toScheme.basicOpen s`. Introduce `U hU s`. Rewrite using `[C.G.toScheme.mem_basicOpen s w hU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Establish `hle : IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) ≤ P`. Use `hco.le.trans (sup_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h1 : w ∉ C.G.toScheme.basicOpen (u i)`. Rewrite using `[← hm W hw]`. Conclude with `hco.ge (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))`.

Establish `e : ∀ t : W.toScheme, t.1 ∈ C.G.toScheme.basicOpen (u i) ↔ f t ∈ Scheme.basicOpen _ (AffineSpace.coord C.Z i)`. Introduce `t`. Establish `e1 : f ⁻¹ᵁ Scheme.basicOpen _ (AffineSpace.coord C.Z i) = W.toScheme.basicOpen (W.topIso.inv.hom (u i))`. Rewrite using `[Scheme.preimage_basicOpen_top, hf, AffineSpace.homOfVector_appTop_coord]`. Establish `e2` using `W.ι_image_basicOpen_topIso_inv (u i)`.

Rewrite using `[← e2, ← e1]`. Conclude with `Scheme.Hom.apply_mem_image_iff W.ι (x := t)`. Use `(hP W hw (u i)).2 ?_` and prove the remaining obligations. Rewrite using `[e y, hfy, ← e ⟨w, hw⟩]`. Conclude with `h1`.

Use `(Ideal.IsPrime.radical_le_iff inferInstance).2 ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Take `⟨V, hV, s, rfl⟩` from `C.Z.presheaf.exists_germ_eq a`. Rewrite using `[Ideal.mem_comap, Scheme.Hom.germ_stalkMap_apply]`.

Use `(hP _ _ _).2 ?_` and prove the remaining obligations. Establish `h1 : C.GG.hom w ∉ C.Z.basicOpen s`. Rewrite using `[C.Z.mem_basicOpen s _ hV]`. Conclude with `ha`. Rewrite `h1` using `[← hg]`.

Introduce `h2`. Apply `h1` to reduce the goal to its premises. Establish `e` using `Scheme.preimage_basicOpen C.GG.hom s`. Conclude with `e.ge h2`. Apply `eq_of_specializes_of_basicOpen hy'` to reduce the goal to its premises.

Introduce `U hU s hs`. Assume the negation of the conclusion as `hn`. Conclude with `(hP U hU s).1 (hle ((hm U hU s).2 hn)) hs`.
-/
theorem quasiFiniteAt_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  intro C w W hw u hcl hco
  have := C.proper
  have hlft : LocallyOfFiniteType C.GG.hom := inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom))
  unfold Core.Coord at hco
  change IsLocalRing.maximalIdeal (C.GG.left.presheaf.stalk w) = _ at hco
  set f := AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i)) with hf
  have hover : f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z) = W.ι ≫ C.GG.hom := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType (f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z)) := by
    rw [hover]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have hemb := W.ι.isOpenEmbedding
  apply quasiFiniteAt_of_isClosed_of_generization
  · have := hcl.preimage hemb.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  intro y hy hfy
  have hy' : y.1 ⤳ w := hy.map hemb.continuous
  have hg : C.GG.hom y.1 = C.GG.hom w := by
    have e : ∀ t : W.toScheme, C.GG.hom t.1 = (𝔸(Fin C.g; C.Z) ↘ C.Z) (f t) := by
      intro t
      rw [← Scheme.Hom.comp_apply, hover]; rfl
    rw [e y, hfy, ← e ⟨w, hw⟩]
  apply Subtype.ext
  let P : Ideal (C.G.toScheme.presheaf.stalk w) :=
    (IsLocalRing.maximalIdeal _).comap (C.G.toScheme.presheaf.stalkSpecializes hy').hom
  have hP : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ P ↔ y.1 ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s y.1 (hy'.mem_open U.2 hU), Ideal.mem_comap,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hm : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ IsLocalRing.maximalIdeal _ ↔
        w ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s w hU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) ≤ P := by
    refine hco.le.trans (sup_le ?_ ?_)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : w ∉ C.G.toScheme.basicOpen (u i) := by
        rw [← hm W hw]
        exact hco.ge (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      have e : ∀ t : W.toScheme, t.1 ∈ C.G.toScheme.basicOpen (u i) ↔
          f t ∈ Scheme.basicOpen _ (AffineSpace.coord C.Z i) := by
        intro t
        have e1 : f ⁻¹ᵁ Scheme.basicOpen _ (AffineSpace.coord C.Z i) =
            W.toScheme.basicOpen (W.topIso.inv.hom (u i)) := by
          rw [Scheme.preimage_basicOpen_top, hf, AffineSpace.homOfVector_appTop_coord]
        have e2 := W.ι_image_basicOpen_topIso_inv (u i)
        rw [← e2, ← e1]
        exact Scheme.Hom.apply_mem_image_iff W.ι (x := t)
      refine (hP W hw (u i)).2 ?_
      rw [e y, hfy, ← e ⟨w, hw⟩]
      exact h1
    · refine (Ideal.IsPrime.radical_le_iff inferInstance).2 ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨V, hV, s, rfl⟩ := C.Z.presheaf.exists_germ_eq a
      rw [Ideal.mem_comap, Scheme.Hom.germ_stalkMap_apply]
      refine (hP _ _ _).2 ?_
      have h1 : C.GG.hom w ∉ C.Z.basicOpen s := by
        rw [C.Z.mem_basicOpen s _ hV]
        exact ha
      rw [← hg] at h1
      intro h2
      apply h1
      have e := Scheme.preimage_basicOpen C.GG.hom s
      exact e.ge h2
  apply eq_of_specializes_of_basicOpen hy'
  intro U hU s hs
  by_contra hn
  exact (hP U hU s).1 (hle ((hm U hU s).2 hn)) hs

end GlobalTheory
