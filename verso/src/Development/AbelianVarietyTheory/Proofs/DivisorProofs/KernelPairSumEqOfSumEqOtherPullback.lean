import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]

/- English proof (translation)
The claim follows from `x.2`.
-/
theorem ι_mem {X : Scheme.{0}} (U : X.Opens) (x : U.toScheme) : U.ι x ∈ U := x.2

/- English proof (translation)
Take `⟨z, h1, h2⟩` from `exists_lift N p hp (VT N V).toScheme (VT N V).ι (VT N V).ι rfl`. Establish `hr : Set.range z ⊆ Set.range (Wk N p hp V).ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show (abP N p hp).left (z x) ∈ VT N V`. Rewrite using `[← Scheme.Hom.comp_apply, h1]`. Conclude with `ι_mem _ x`. Use `show (cdP N p hp).left (z x) ∈ VT N V`. Rewrite using `[← Scheme.Hom.comp_apply, h2]`.

Conclude with `ι_mem _ x`. Set `z'` to `IsOpenImmersion.lift (Wk N p hp V).ι z hr`. Establish `e : z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, ← h1, Category.assoc, Over.w (abP N p hp)]`. Establish `: Surjective (z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom)` using `by rw [e]; exact h`.

Conclude with `Surjective.of_comp z' _`.
-/
theorem surjective_Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (V : (N.U ⊗ N.U).left.Opens) (h : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)) :
    Surjective ((Wk N p hp V).ι ≫ (Pk N p hp).hom) := by
  obtain ⟨z, h1, h2⟩ := exists_lift N p hp (VT N V).toScheme (VT N V).ι (VT N V).ι rfl
  have hr : Set.range z ⊆ Set.range (Wk N p hp V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · show (abP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h1]; exact ι_mem _ x
    · show (cdP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h2]; exact ι_mem _ x
  let z' := IsOpenImmersion.lift (Wk N p hp V).ι z hr
  have e : z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ← h1, Category.assoc, Over.w (abP N p hp)]
  have : Surjective (z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom) := by rw [e]; exact h
  exact Surjective.of_comp z' _

/- English proof (translation)
Set `a'` to `IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (abP N p hp).left) (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(ι_mem _ x).1)`. Set `c'` to `IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (cdP N p hp).left) (by`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(ι_mem _ x).2)`. Establish `ea : a' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (abP N p hp).left` using `IsOpenImmersion.lift_fac _ _ _`. Establish `ec : c' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (cdP N p hp).left` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `e0` using `congrArg (fun f => (Wk N p hp V).ι ≫ Over.Hom.left f) (abP_sum N p hp)`. Simplify using `only [Over.comp_left] at e0`. Establish `hemb` using `GlobalTheory.Mum.DescHom.isOpenImmersion_emb N p hp`. Establish `e2 : a' ≫ mT N V m hm = c' ≫ mT N V m hm`. Use `(cancel_mono (Desc.emb N p hp).left).1 ?_` and prove the remaining obligations.

Simplify using `only [Category.assoc]`. Rewrite using `[← h, ← Category.assoc, ea, ← Category.assoc, ec, Category.assoc, Category.assoc]`. Conclude with `e0`. Simplify using `only [Over.comp_left]`. Rewrite using `[← Category.assoc, ← ea, Category.assoc, h', ← Category.assoc, e2, Category.assoc, ← h', ← Category.assoc, ec, Category.assoc]`.
-/
theorem agree_Wk (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (hp' : p' ≫ π = pullback.fst π π ≫ π)
    (h : (VT N V).ι ≫ (Desc.sum N p hp).left = mT N V m hm ≫ (Desc.emb N p hp).left)
    (h' : (VT N V).ι ≫ (Desc.sum N p' hp').left = mT N V m hm ≫ (Desc.emb N p' hp').left) :
    (Wk N p hp V).ι ≫ (abP N p hp ≫ Desc.sum N p' hp').left =
      (Wk N p hp V).ι ≫ (cdP N p hp ≫ Desc.sum N p' hp').left := by
  let a' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (abP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).1)
  let c' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (cdP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).2)
  have ea : a' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (abP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have ec : c' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (cdP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have e0 := congrArg (fun f => (Wk N p hp V).ι ≫ Over.Hom.left f) (abP_sum N p hp)
  simp only [Over.comp_left] at e0
  have hemb := GlobalTheory.Mum.DescHom.isOpenImmersion_emb N p hp
  have e2 : a' ≫ mT N V m hm = c' ≫ mT N V m hm := by
    refine (cancel_mono (Desc.emb N p hp).left).1 ?_
    simp only [Category.assoc]
    rw [← h, ← Category.assoc, ea, ← Category.assoc, ec, Category.assoc, Category.assoc]
    exact e0
  simp only [Over.comp_left]
  rw [← Category.assoc, ← ea, Category.assoc, h', ← Category.assoc, e2, Category.assoc, ← h', ← Category.assoc, ec,
    Category.assoc]

end GlobalTheory.Mum.DescKP

open GlobalTheory.Mum.DescKP in

/- English proof (translation)
Introduce `R _ _ _ _ S π _ _ _ G _ _ hG N hLaw p p' hp hp' Z g g' hgg`. Take `⟨V, m, hV, hm, hL⟩` from `hLaw`. Establish `hlaw` using `fun (q : pullback π π ⟶ S) (hq : q ≫ π = pullback.fst π π ≫ π) => GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication N V m hm hL q hq`. Establish `: Smooth N.U.hom` using `N.smooth`. Establish `: Surjective N.U.hom` using `DescHom.surjective_near N`.

Establish `: Smooth G.hom` using `hG.smooth`. Establish `: IsSeparated G.hom` using `hG.separated`. Use `DescHom.geometricallyIrreducible_of_semiAbelian G hG` as an intermediate fact. Establish `sV` using `GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square N.U N.smooth inferInstance V hV`. Establish `sq : IsPullback (DescKP.pairU N ∣_ V) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) (V.ι ≫ (N.U ⊗ N.U).hom) (pullback.fst π π ≫ π)` using `(isPullback_morphismRestrict (DescKP.pairU N) V).paste_vert (GlobalTheory.T.isPullback_descentSquarePairToOpenSquare N)`.

Establish `sVT : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)` using `MorphismProperty.of_isPullback (P := @Surjective) sq sV`. Establish `sW` using `DescKP.surjective_Wk N p hp V sVT`. Establish `: Smooth (Desc.UT N).hom` using `inferInstanceAs (Smooth (pullback.snd N.U.hom (pullback.fst π π ≫ π)))`. Establish `: Surjective (Desc.UT N).hom` using `inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))`. Establish `hGp : GeometricallyIrreducible ((Over.pullback p).obj G).hom` using `inferInstanceAs (GeometricallyIrreducible (pullback.snd G.hom p))`.

Use `DescHom.isOpenImmersion_emb N p hp` as an intermediate fact. Establish `: GeometricallyIrreducible (Desc.UT N).hom`. Establish `e : (Desc.emb N p hp).left ≫ ((Over.pullback p).obj G).hom = (Desc.UT N).hom` using `Over.w _`. Establish `h` using `GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (Desc.emb N p hp).left inferInstance _ hGp (by rw [e]; infer_instance)`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Establish `: Smooth (Desc.UT N ⊗ Desc.UT N).hom` using `inferInstanceAs (Smooth (pullback.fst (Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N).hom))`. Establish `: GeometricallyIrreducible (Desc.UT N ⊗ Desc.UT N).hom` using `GeometricallyIrreducible.comp (pullback.fst (Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N).hom`. Establish `: Smooth ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom` using `inferInstanceAs (Smooth (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N ⊗ Desc.UT N).hom))`. Establish `h3 : GeometricallyIrreducible ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom` using `GeometricallyIrreducible.comp (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N ⊗ Desc.UT N).hom`. Establish `: Surjective (DescKP.Pk N p hp).hom` using `Surjective.of_comp (DescKP.Wk N p hp V).ι _`.

Establish `: Smooth (DescKP.Pk N p hp).hom` using `inferInstanceAs (Smooth (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left ≫ ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom))`. Establish `: GeometricallyIrreducible (DescKP.Pk N p hp).hom` using `GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left) inferInstance _ h3 (inferInstanceAs (Surjective (DescKP.Pk N p hp).hom))`. Establish `: IsSeparated ((Over.pullback p').obj G).hom` using `inferInstanceAs (IsSeparated (pullback.snd G.hom p'))`. Set `j : Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom) ⟶ DescKP.Pk N p hp` to `Over.homMk (DescKP.Wk N p hp V).ι rfl`. Establish `: IsOpenImmersion j.left` using `inferInstanceAs (IsOpenImmersion (DescKP.Wk N p hp V).ι)`.

Establish `: Surjective (Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom)).hom` using `sW`. Establish `hF : DescKP.abP N p hp ≫ Desc.sum N p' hp' = DescKP.cdP N p hp ≫ Desc.sum N p' hp'`. Use `DescHom.ext_of_open j ?_` and prove the remaining obligations. Use `ext1`. Conclude with `DescKP.agree_Wk N V m hm p p' hp hp' (hlaw p hp) (hlaw p' hp')`.

Take `⟨z, hz, hz'⟩` from `DescKP.exists_lift N p hp Z g g' hgg`. Rewrite using `[← hz, ← hz', Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hF]`.
-/
theorem GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  intro R _ _ _ _ S π _ _ _ G _ _ hG N hLaw p p' hp hp' Z g g' hgg
  obtain ⟨V, m, hV, hm, hL⟩ := hLaw
  have hlaw := fun (q : pullback π π ⟶ S) (hq : q ≫ π = pullback.fst π π ≫ π) => GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication N V m hm hL q hq
  have : Smooth N.U.hom := N.smooth
  have : Surjective N.U.hom := DescHom.surjective_near N
  have : Smooth G.hom := hG.smooth
  have : IsSeparated G.hom := hG.separated
  have := DescHom.geometricallyIrreducible_of_semiAbelian G hG

  have sV := GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square N.U N.smooth inferInstance V hV
  have sq : IsPullback (DescKP.pairU N ∣_ V) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
      (V.ι ≫ (N.U ⊗ N.U).hom) (pullback.fst π π ≫ π) :=
    (isPullback_morphismRestrict (DescKP.pairU N) V).paste_vert (GlobalTheory.T.isPullback_descentSquarePairToOpenSquare N)
  have sVT : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq sV
  have sW := DescKP.surjective_Wk N p hp V sVT

  have : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have : Surjective (Desc.UT N).hom := inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have hGp : GeometricallyIrreducible ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd G.hom p))
  have := DescHom.isOpenImmersion_emb N p hp
  have : GeometricallyIrreducible (Desc.UT N).hom := by
    have e : (Desc.emb N p hp).left ≫ ((Over.pullback p).obj G).hom = (Desc.UT N).hom := Over.w _
    have h := GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (Desc.emb N p hp).left inferInstance _ hGp (by rw [e]; infer_instance)
    rwa [e] at h
  have : Smooth (Desc.UT N ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N).hom))
  have : GeometricallyIrreducible (Desc.UT N ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N).hom
  have : Smooth ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N ⊗ Desc.UT N).hom))
  have h3 : GeometricallyIrreducible ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N ⊗ Desc.UT N).hom
  have : Surjective (DescKP.Pk N p hp).hom := Surjective.of_comp (DescKP.Wk N p hp V).ι _
  have : Smooth (DescKP.Pk N p hp).hom :=
    inferInstanceAs (Smooth (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left ≫
      ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom))
  have : GeometricallyIrreducible (DescKP.Pk N p hp).hom :=
    GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left) inferInstance _ h3
      (inferInstanceAs (Surjective (DescKP.Pk N p hp).hom))
  have : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))

  let j : Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom) ⟶ DescKP.Pk N p hp :=
    Over.homMk (DescKP.Wk N p hp V).ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (DescKP.Wk N p hp V).ι)
  have : Surjective (Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom)).hom := sW
  have hF : DescKP.abP N p hp ≫ Desc.sum N p' hp' = DescKP.cdP N p hp ≫ Desc.sum N p' hp' := by
    refine DescHom.ext_of_open j ?_
    ext1
    exact DescKP.agree_Wk N V m hm p p' hp hp' (hlaw p hp) (hlaw p' hp')
  obtain ⟨z, hz, hz'⟩ := DescKP.exists_lift N p hp Z g g' hgg
  rw [← hz, ← hz', Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hF]
