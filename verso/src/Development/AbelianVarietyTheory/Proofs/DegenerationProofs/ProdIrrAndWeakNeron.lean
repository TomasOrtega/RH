import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

/- English proof (translation)
Establish `irr : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsIrreducible (f ⁻¹' Set.range i) → IrreducibleSpace ↥(pullback f i)`. Introduce `X f h`. Rewrite `h` using `[← Scheme.Pullback.range_fst]`. Establish `e` using `(pullback.fst f i).isClosedEmbedding.isEmbedding`. Use `Subtype.irreducibleSpace h` as an intermediate fact.

Conclude with `e.toHomeomorph.irreducibleSpace_iff.2 this`. Establish `h1` using `irr f hf`. Establish `h2` using `irr g hg`. Establish `h3 : GeometricallyIrreducible (pullback.snd f i)` using `geometricallyIrreducible_of_isAlgClosed _`. Establish `h4 : IrreducibleSpace ↥(pullback (pullback.snd f i) (pullback.snd g i))` using `inferInstance`.

Set `m` to `pullback.map (pullback.snd f i) (pullback.snd g i) f g (pullback.fst f i) (pullback.fst g i) i pullback.condition.symm pullback.condition.symm`. Establish `hm : Set.range m = (pullback.fst f g ≫ f) ⁻¹' Set.range i`. Rewrite using `[Scheme.Pullback.range_map, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]`. Use extensionality with `z`. Establish `hz : g (pullback.snd f g z) = f (pullback.fst f g z)`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply, hz, and_self]`. Rewrite using `[← hm, ← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ m.continuous.continuousOn`.
-/
theorem isIrreducible_fibre_pullback {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f]
    {k : Type} [Field k] [IsAlgClosed k] (i : Spec (.of k) ⟶ S) [IsClosedImmersion i]
    (hf : IsIrreducible (f ⁻¹' Set.range i)) (hg : IsIrreducible (g ⁻¹' Set.range i)) :
    IsIrreducible ((pullback.fst f g ≫ f) ⁻¹' Set.range i) := by
  have irr : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsIrreducible (f ⁻¹' Set.range i) →
      IrreducibleSpace ↥(pullback f i) := by
    intro X f h
    rw [← Scheme.Pullback.range_fst] at h
    have e := (pullback.fst f i).isClosedEmbedding.isEmbedding
    have := Subtype.irreducibleSpace h
    exact e.toHomeomorph.irreducibleSpace_iff.2 this
  have h1 := irr f hf
  have h2 := irr g hg
  have h3 : GeometricallyIrreducible (pullback.snd f i) := geometricallyIrreducible_of_isAlgClosed _
  have h4 : IrreducibleSpace ↥(pullback (pullback.snd f i) (pullback.snd g i)) := inferInstance
  let m := pullback.map (pullback.snd f i) (pullback.snd g i) f g (pullback.fst f i) (pullback.fst g i) i
    pullback.condition.symm pullback.condition.symm
  have hm : Set.range m = (pullback.fst f g ≫ f) ⁻¹' Set.range i := by
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    ext z
    have hz : g (pullback.snd f g z) = f (pullback.fst f g z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply, hz, and_self]
  rw [← hm, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ m.continuous.continuousOn

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

/- English proof (translation)
Establish `h2` using `congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h`. Establish `h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K)) = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left` using `pullback.lift_fst _ _ _`. Simplify using `only [Over.comp_left, Category.assoc] at h2`. Unfold `Model.j`. Rewrite using `[Category.assoc]`.

Conclude with `(congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2`.
-/
theorem Model.j_comp_of_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) :
    M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

/- English proof (translation)
The claim follows from `Model.j_comp_of_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])`.
-/
theorem Model.prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  Model.j_comp_of_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

/- English proof (translation)
The claim follows from `Model.j_comp_of_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])`.
-/
theorem Model.prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  Model.j_comp_of_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

/- English proof (translation)
Establish `: Set.range (spMap (IsLocalRing.residue R)) = {IsLocalRing.closedPoint R}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[Subsingleton.elim y (IsLocalRing.closedPoint _)]`.

Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue R)`. Introduce and unpack `rfl`. Conclude with `⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem Model.sp_eq_preimage [IsLocalRing R] (M : Model R A) :
    M.sp = M.Y.hom ⁻¹' Set.range (spMap (IsLocalRing.residue R)) := by
  have : Set.range (spMap (IsLocalRing.residue R)) = {IsLocalRing.closedPoint R} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint _)]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩
  rw [this]; rfl

/- English proof (translation)
Use `M.smooth` as an intermediate fact. Establish `: IsClosedImmersion (spMap (IsLocalRing.residue R))` using `IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective`. Unfold `Model.Irr at *`. Rewrite `*` using `[Model.sp_eq_preimage]`. Conclude with `isIrreducible_fibre_pullback M.Y.hom N.Y.hom (spMap (IsLocalRing.residue R)) hM hN`.
-/
theorem Model.Irr.prod [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] {M : Model R A} {N : Model R A'}
    (hM : M.Irr) (hN : N.Irr) : (M.prod N).Irr := by
  have := M.smooth
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  unfold Model.Irr at *
  rw [Model.sp_eq_preimage] at *
  exact isIrreducible_fibre_pullback M.Y.hom N.Y.hom (spMap (IsLocalRing.residue R)) hM hN

/- English proof (translation)
Introduce `R' K' _ _ _ _ _ _ _ hm a ha`. Take `⟨i, b, hb, hb'⟩` from `hM R' K' hm (a ≫ (fst A A').left) (by`. Rewrite using `[Category.assoc, ← ha, ← Over.w (fst A A'), Category.assoc])`. Take `⟨i', c, hc, hc'⟩` from `hN R' K' hm (a ≫ (snd A A').left) (by`. Rewrite using `[Category.assoc, ← ha, ← Over.w (snd A A'), Category.assoc])`.

Establish `e1` using `Model.prod_j_fst (M i) (N i')`. Establish `e2` using `Model.prod_j_snd (M i) (N i')`. Use `⟨(i, i'), pullback.lift (f := (M i).Y.hom) (g := (N i').Y.hom) b c (hb.trans hc.symm), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(pullback.lift_fst_assoc _ _ _ _).trans hb`. Use `pullback.hom_ext (f := (M i).Y.hom) (g := (N i').Y.hom) ?_ ?_` and prove the remaining obligations.

Use `((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm` and prove the remaining obligations. Use `(congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (hb'.trans ?_)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans (congrArg (a ≫ ·) e1.symm)`. Use `((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm` and prove the remaining obligations. Use `(congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans (hc'.trans ?_)` and prove the remaining obligations.

Conclude with `(Category.assoc _ _ _).trans (congrArg (a ≫ ·) e2.symm)`.
-/
theorem WeakNeron.prod [IsLocalRing R] {I I' : Type} {M : I → Model R A} {N : I' → Model R A'}
    (hM : WeakNeron M) (hN : WeakNeron N) : WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R' K' _ _ _ _ _ _ _ hm a ha
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' hm (a ≫ (fst A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (fst A A'), Category.assoc])
  obtain ⟨i', c, hc, hc'⟩ := hN R' K' hm (a ≫ (snd A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (snd A A'), Category.assoc])
  have e1 := Model.prod_j_fst (M i) (N i')
  have e2 := Model.prod_j_snd (M i) (N i')
  refine ⟨(i, i'), pullback.lift (f := (M i).Y.hom) (g := (N i').Y.hom) b c (hb.trans hc.symm), ?_, ?_⟩
  · exact (pullback.lift_fst_assoc _ _ _ _).trans hb
  · refine pullback.hom_ext (f := (M i).Y.hom) (g := (N i').Y.hom) ?_ ?_
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (hb'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e1.symm)
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans (hc'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e2.symm)

/- English proof (translation)
Introduce `R K _ _ _ _ _ h A A'`. Use `h.2.2.1` as an intermediate fact. Conclude with `⟨fun _ _ hM hN => hM.prod hN, fun _ _ _ _ hM hN => hM.prod hN⟩`.
-/
theorem prod_irr_and_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' : Over (Sp K)), (∀ (M : Model R A) (N : Model R A'), M.Irr → N.Irr → (M.prod N).Irr) ∧ ∀ (I I' : Type) (M : I → Model R A) (N : I' → Model R A'), WeakNeron M → WeakNeron N → WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R K _ _ _ _ _ h A A'
  have := h.2.2.1
  exact ⟨fun _ _ hM hN => hM.prod hN, fun _ _ _ _ hM hN => hM.prod hN⟩

end GlobalTheory.SS
