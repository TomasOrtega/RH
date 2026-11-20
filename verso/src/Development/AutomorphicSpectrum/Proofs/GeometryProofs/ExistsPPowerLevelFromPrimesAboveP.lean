import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitCompsOfIsTowerOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SplitEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Establish `b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)`. Conclude with `MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁`.
-/
theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁

/- English proof (translation)
Establish `hfin : (irreducibleComponents X).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`. Establish `hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x}`. Introduce `C hC hxC`. Establish `hg` using `hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)`. Establish `e` using `hx _ (hg.specializes hxC)`.

Rewrite using `[← e]`. Conclude with `hg.def.symm`. Set `T : Set X` to `⋃ C ∈ irreducibleComponents X \ {closure {x}}, C`. Establish `hT : IsClosed T` using `Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset) fun C hC => isClosed_of_mem_irreducibleComponents C hC.1`. Establish `hxT : x ∈ Tᶜ`.

Introduce `h`. Take `⟨C, ⟨hC, hne⟩, hxC⟩` from `Set.mem_iUnion₂.1 h`. Conclude with `hne (hgen C hC hxC)`. Take `⟨w, hwT, hwU⟩` from `hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩`. Establish `hwC : w ∈ closure {x}`.

Assume the negation of the conclusion as `hn`. Use `hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)` and prove the remaining obligations. Rewrite using `[← (show irreducibleComponent w = closure {x} from e)]`. Conclude with `mem_irreducibleComponent`. Conclude with `(specializes_iff_mem_closure.2 hwC).mem_open hU hwU`.
-/
theorem mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [T0Space X] {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : ∀ z, z ⤳ x → z = x) : x ∈ U := by
  have hfin : (irreducibleComponents X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x} := by
    intro C hC hxC
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have e := hx _ (hg.specializes hxC)
    rw [← e]
    exact hg.def.symm
  let T : Set X := ⋃ C ∈ irreducibleComponents X \ {closure {x}}, C
  have hT : IsClosed T := Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hxT : x ∈ Tᶜ := by
    intro h
    obtain ⟨C, ⟨hC, hne⟩, hxC⟩ := Set.mem_iUnion₂.1 h
    exact hne (hgen C hC hxC)
  obtain ⟨w, hwT, hwU⟩ := hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩
  have hwC : w ∈ closure {x} := by
    by_contra hn
    refine hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w,
      ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)
    rw [← (show irreducibleComponent w = closure {x} from e)]
    exact mem_irreducibleComponent
  exact (specializes_iff_mem_closure.2 hwC).mem_open hU hwU

/- English proof (translation)
Use `isPreimmersion_fst Y` as an intermediate fact. Use `Y.jQ_open` as an intermediate fact. Establish `: IsPreimmersion Y.j` using `by unfold Model.j; infer_instance`. Conclude with `Y.j.isEmbedding.injective`.
-/
theorem injective_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Function.Injective Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  exact Y.j.isEmbedding.injective

/- English proof (translation)
The claim follows from `Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))`.
-/
theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (g : X ⟶ X') :
    genPt (ξ ≫ g) = g (genPt ξ) :=
  Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))

/- English proof (translation)
Establish `hpr` using `projProper _ _ _ Y.proj`. Establish `sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F)` using `by rw [hs, spMap_comp']`. Set `P` to `pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))`. Set `ξ₁ : Spec (CommRingCat.of Ω) ⟶ P` to `pullback.lift ξ (spMap cst) sq`. Establish `hf : ξ₁ ≫ pullback.fst _ _ = ξ` using `pullback.lift_fst _ _ _`.

Set `pt : Spec (CommRingCat.of Ω)` to `IsLocalRing.closedPoint Ω`. Set `x₁ : P` to `ξ₁ pt`. Establish `h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ`. Establish `e` using `Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt`. Rewrite `e` using `[hf]`.

Conclude with `e.symm`. Establish `a₁` using `isPreimmersion_fst Y`. Establish `hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁`. Introduce `z hz`. Apply `(pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective` to reduce the goal to its premises.

Rewrite using `[h1]`. Conclude with `hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)`. Establish `: LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `inferInstance`. Establish `: QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `inferInstance`. Establish `: IsLocallyNoetherian P` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))`.

Establish `: CompactSpace P` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))`. Establish `: IsNoetherian P` using `{}`. Use `Y.jQ_open` as an intermediate fact. Take `⟨v', hv'⟩` from `mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁`. Conclude with `⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩`.
-/
theorem mem_range_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω) (hmax : ∀ y, y ⤳ genPt ξ → y = genPt ξ)
    (hs : ξ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) : genPt ξ ∈ Set.range Y.j := by
  have hpr := projProper _ _ _ Y.proj
  have sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp']
  let P := pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let ξ₁ : Spec (CommRingCat.of Ω) ⟶ P := pullback.lift ξ (spMap cst) sq
  have hf : ξ₁ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  let x₁ : P := ξ₁ pt
  have h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ := by
    have e := Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt
    rw [hf] at e
    exact e.symm
  have a₁ := isPreimmersion_fst Y
  have hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁ := by
    intro z hz
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective
    rw [h1]
    exact hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
  have : LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian P := {}
  have := Y.jQ_open
  obtain ⟨v', hv'⟩ := mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩

/- English proof (translation)
Introduce `Ω _ ξ cst hξ hs a ha`. Establish `hmax` using `CptInh.nogen ξ hξ`. Take `⟨w₀, hw₀⟩` from `mem_range_j Y ξ cst hmax hs`. Establish `hwmax : ∀ y, y ⤳ w₀ → y = w₀`. Introduce `y hy`.

Establish `h1 : Y.j y ⤳ genPt ξ` using `hw₀ ▸ hy.map Y.j.continuous`. Conclude with `injective_j Y ((hmax _ h1).trans hw₀.symm)`. Set `Z : Formalism.L2.Pj.Comp Xo c` to `⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩`. Establish `hZ : Formalism.L2.Pj.genPt Z = w₀`. Establish `hC` using `irreducibleComponent_mem_irreducibleComponents w₀`.

Establish `hg` using `hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)`. Conclude with `hwmax _ (hg.specializes mem_irreducibleComponent)`. Establish `e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ`. Use `(genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_` and prove the remaining obligations. Rewrite using `[← hw₀, ← hZ]`.

Conclude with `congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)`. Take `⟨i, hi⟩` from `TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e`. Establish `hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z)`. Establish `hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`.

Establish `h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z))` using `(Spec.map_preimage _).symm`. Establish `h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) = spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F))`. Rewrite using `[← h1, ← hs]`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Use `Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_` and prove the remaining obligations.

Use `(Category.assoc _ _ _).symm.trans ?_` and prove the remaining obligations. Conclude with `(congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)`. Establish `e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) = (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F)`. Apply `TowerOfTest.spec_inj` to reduce the goal to its premises. Establish `: spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) = spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F))`.

Rewrite using `[RingHom.comp_assoc, spMap_comp']`. Conclude with `this.trans (h2.symm.trans (spMap_comp' _ _).symm)`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0`. Establish `hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a))`. Take `⟨p, hp0, hp⟩` from `ha`.

Use `⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩` and prove the remaining obligations. Establish `h3` using `Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a`. Rewrite `h3` using `[← Polynomial.aeval_def, hp, map_zero]`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Use `Eq.trans ?_ h3.symm` and prove the remaining obligations.

Conclude with `congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)`. Take `⟨k, hk⟩` from `hc Z _ hb`. Use `⟨k, i.injective ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a`. Apply `(algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective` to reduce the goal to its premises.

Rewrite using `[← hk, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[← h2, ← hcomp]`. Both sides reduce to the same expression.
-/
theorem splitComps_of_fnAlgClosed (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hc : Formalism.L2.Pj.FnAlgClosed Xo c) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have hmax := CptInh.nogen ξ hξ
  obtain ⟨w₀, hw₀⟩ := mem_range_j Y ξ cst hmax hs
  have hwmax : ∀ y, y ⤳ w₀ → y = w₀ := by
    intro y hy
    have h1 : Y.j y ⤳ genPt ξ := hw₀ ▸ hy.map Y.j.continuous
    exact injective_j Y ((hmax _ h1).trans hw₀.symm)
  let Z : Formalism.L2.Pj.Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hZ : Formalism.L2.Pj.genPt Z = w₀ := by
    have hC := irreducibleComponent_mem_irreducibleComponents w₀
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    exact hwmax _ (hg.specializes mem_irreducibleComponent)
  have e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ := by
    refine (genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_
    rw [← hw₀, ← hZ]
    exact congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, hi⟩ := TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e
  have hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) =
        spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← hs]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)
    have e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) =
        (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F) := by
      apply TowerOfTest.spec_inj
      have : spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
        rw [RingHom.comp_assoc, spMap_comp']
      exact this.trans (h2.symm.trans (spMap_comp' _ _).symm)
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a)) := by
    obtain ⟨p, hp0, hp⟩ := ha
    refine ⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩
    have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a
    rw [← Polynomial.aeval_def, hp, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Eq.trans ?_ h3.symm
    exact congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.SplitEx
