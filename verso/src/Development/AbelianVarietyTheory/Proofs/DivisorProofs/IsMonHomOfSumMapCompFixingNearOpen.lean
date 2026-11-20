import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfAgreeOnFibreDenseOpenSmoothStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescHom

/- English proof (translation)
Establish `hfib : ∀ x : X.left, x ∈ closure ((j.left.opensRange : Set X.left) ∩ X.hom ⁻¹' {X.hom x})`. Introduce `x`. Establish `hirr : IsIrreducible (X.hom ⁻¹' {X.hom x})` using `X.hom.isIrreducible_preimage X.hom.isOpenMap isIrreducible_singleton`. Take `⟨w, hw⟩` from `W.hom.surjective (X.hom x)`. Establish `hne : (X.hom ⁻¹' {X.hom x} ∩ (j.left.opensRange : Set X.left)).Nonempty`.

Use `⟨j.left w, ?_, ⟨w, rfl⟩⟩` and prove the remaining obligations. Use `show X.hom (j.left w) = X.hom x`. Rewrite using `[← Scheme.Hom.comp_apply, Over.w]`. Conclude with `hw`. Establish `hsub` using `subset_closure_inter_of_isPreirreducible_of_isOpen hirr.isPreirreducible j.left.opensRange.isOpen hne (show x ∈ X.hom ⁻¹' {X.hom x} from rfl)`.

Rewrite `hsub` using `[Set.inter_comm]`. Then use the resulting hypothesis. Establish `hl : j.left ≫ f.left = j.left ≫ g.left`. Simplify `congrArg CommaMorphism.left h` using `only [Over.comp_left]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `GlobalTheory.FibreDense.main X.left T Y.left X.hom Y.hom j.left.opensRange hfib f.left g.left (by rw [Over.w f, Over.w g]) ?_` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, hl]`.
-/
theorem ext_of_open {T : Scheme.{0}} {W X Y : Over T} (j : W ⟶ X) [IsOpenImmersion j.left] [Surjective W.hom]
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y} (h : j ≫ f = j ≫ g) : f = g := by
  have hfib : ∀ x : X.left, x ∈ closure ((j.left.opensRange : Set X.left) ∩ X.hom ⁻¹' {X.hom x}) := by
    intro x
    have hirr : IsIrreducible (X.hom ⁻¹' {X.hom x}) :=
      X.hom.isIrreducible_preimage X.hom.isOpenMap isIrreducible_singleton
    obtain ⟨w, hw⟩ := W.hom.surjective (X.hom x)
    have hne : (X.hom ⁻¹' {X.hom x} ∩ (j.left.opensRange : Set X.left)).Nonempty := by
      refine ⟨j.left w, ?_, ⟨w, rfl⟩⟩
      show X.hom (j.left w) = X.hom x
      rw [← Scheme.Hom.comp_apply, Over.w]
      exact hw
    have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.isPreirreducible
      j.left.opensRange.isOpen hne (show x ∈ X.hom ⁻¹' {X.hom x} from rfl)
    rwa [Set.inter_comm] at hsub
  have hl : j.left ≫ f.left = j.left ≫ g.left := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  refine GlobalTheory.FibreDense.main X.left T Y.left X.hom Y.hom j.left.opensRange hfib f.left g.left
    (by rw [Over.w f, Over.w g]) ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, hl]

/- English proof (translation)
Establish `hmuX : (μ : X ⊗ X ⟶ X) = fst X X * snd X X`. Rewrite using `[Hom.mul_def, lift_fst_snd, Category.id_comp]`. Establish `hmuY : (μ : Y ⊗ Y ⟶ Y) = fst Y Y * snd Y Y`. Rewrite using `[Hom.mul_def, lift_fst_snd, Category.id_comp]`. Establish `hoi : IsOpenImmersion (j ⊗ₘ j).left`.

Rewrite using `[Over.tensorHom_left]`. Conclude with `MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (by simp) (by simp)`. Establish `hsurj : Surjective (W ⊗ W).hom`. Rewrite using `[Over.tensorObj_hom]`. Use `infer_instance`.

Establish `hsm : Smooth (X ⊗ X).hom`. Rewrite using `[Over.tensorObj_hom]`. Use `infer_instance`. Establish `hgi : GeometricallyIrreducible (X ⊗ X).hom`. Rewrite using `[Over.tensorObj_hom]`.

Conclude with `GeometricallyIrreducible.comp _ _`. Establish `hmul : μ ≫ φ = (φ ⊗ₘ φ) ≫ μ`. Apply `ext_of_open (j ⊗ₘ j)` to reduce the goal to its premises. Establish `lhs : (j ⊗ₘ j) ≫ μ ≫ φ = ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ`. Rewrite using `[hmuX, ← Category.assoc, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]`.

Establish `rhs : (j ⊗ₘ j) ≫ (φ ⊗ₘ φ) ≫ μ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ)`. Rewrite using `[hmuY, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc]`. Rewrite using `[lhs, rhs, h]`. Establish `hcomp : ∀ {Z : Over T} (a b : Z ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ)`. Introduce `Z a b`.

Rewrite using `[Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]`. Establish `hone : η ≫ φ = η`. Establish `h1 : ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) * ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) = (1 : 𝟙_ (Over T) ⟶ X) ≫ φ`. Rewrite using `[← hcomp, _root_.mul_one]`. Establish `h2 : (1 : 𝟙_ (Over T) ⟶ X) ≫ φ = 1` using `_root_.mul_eq_left.mp h1`.

Establish `e1 : ∀ {M : Over T} [MonObj M], (1 : 𝟙_ (Over T) ⟶ M) = η`. Introduce `M _`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Rewrite using `[← e1, ← e1]`. Conclude with `h2`.

Conclude with `⟨hone, hmul⟩`.
-/
theorem isMonHom_of_open {T : Scheme.{0}} {W X Y : Over T} [GrpObj X] [GrpObj Y] (j : W ⟶ X) [IsOpenImmersion j.left]
    [Surjective W.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] (φ : X ⟶ Y)
    (h : ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ)) : IsMonHom φ := by
  have hmuX : (μ : X ⊗ X ⟶ X) = fst X X * snd X X := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hmuY : (μ : Y ⊗ Y ⟶ Y) = fst Y Y * snd Y Y := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hoi : IsOpenImmersion (j ⊗ₘ j).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (by simp) (by simp)
  have hsurj : Surjective (W ⊗ W).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hsm : Smooth (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hgi : GeometricallyIrreducible (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp _ _
  have hmul : μ ≫ φ = (φ ⊗ₘ φ) ≫ μ := by
    apply ext_of_open (j ⊗ₘ j)
    have lhs : (j ⊗ₘ j) ≫ μ ≫ φ = ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ := by
      rw [hmuX, ← Category.assoc, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    have rhs : (j ⊗ₘ j) ≫ (φ ⊗ₘ φ) ≫ μ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ) := by
      rw [hmuY, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_mul, tensorHom_fst_assoc,
        tensorHom_snd_assoc]
    rw [lhs, rhs, h]
  have hcomp : ∀ {Z : Over T} (a b : Z ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ) := by
    intro Z a b
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]
  have hone : η ≫ φ = η := by
    have h1 : ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) * ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) = (1 : 𝟙_ (Over T) ⟶ X) ≫ φ := by
      rw [← hcomp, _root_.mul_one]
    have h2 : (1 : 𝟙_ (Over T) ⟶ X) ≫ φ = 1 := _root_.mul_eq_left.mp h1
    have e1 : ∀ {M : Over T} [MonObj M], (1 : 𝟙_ (Over T) ⟶ M) = η := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← e1, ← e1]
    exact h2
  exact ⟨hone, hmul⟩

/- English proof (translation)
Take `⟨_, hsm, _, _, hgc, _⟩` from `hG`. Use `GlobalTheory.grpObj_geometricallyIntegral_of_smooth S G` as an intermediate fact. Use `infer_instance`.
-/
theorem geometricallyIrreducible_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) :
    GeometricallyIrreducible G.hom := by
  obtain ⟨_, hsm, _, _, hgc, _⟩ := hG
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S G
  infer_instance

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

/- English proof (translation)
Use `N.smooth` as an intermediate fact. Establish `hcl : closedPoint R ∈ Set.range N.U.hom`. Take `⟨s, hs⟩` from `π.surjective (closedPoint R)`. Establish `he : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S` using `Over.w η[G]`. Establish `hGs : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s`.

Rewrite using `[← Scheme.Hom.comp_apply, he]`. Both sides reduce to the same expression. Take `⟨y, hy⟩` from `N.all _ (by rw [hGs, hs])`. Use `⟨pullback.fst N.U.hom π y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over, Scheme.Hom.comp_apply, hy, hGs, hs]`.

Conclude with `⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range (specializes_closedPoint x) hcl⟩`.
-/
theorem surjective_near [GrpObj G] [Surjective π] (N : Near π G) : Surjective N.U.hom := by
  have := N.smooth
  have hcl : closedPoint R ∈ Set.range N.U.hom := by
    obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
    have he : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w η[G]
    have hGs : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s := by
      rw [← Scheme.Hom.comp_apply, he]; rfl
    obtain ⟨y, hy⟩ := N.all _ (by rw [hGs, hs])
    refine ⟨pullback.fst N.U.hom π y, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over,
      Scheme.Hom.comp_apply, hy, hGs, hs]
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (specializes_closedPoint x) hcl⟩

/- English proof (translation)
Establish `hA : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (pullback.snd N.U.hom π) p`. Establish `outer : IsPullback (Desc.toS N p hp ≫ pullback.fst N.U.hom π) (pullback.snd N.U.hom (pullback.fst π π ≫ π)) N.U.hom (p ≫ π)`. Rewrite using `[Desc.toS, pullback.lift_fst, hp]`. Conclude with `IsPullback.of_hasPullback _ _`. Conclude with `IsPullback.of_right outer (by rw [Desc.toS, pullback.lift_snd]) (IsPullback.of_hasPullback _ _)`.

Use `IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback G.hom p)` and prove the remaining obligations. Rewrite using `[Desc.embL, pullback.lift_snd, N.u_over]`. Conclude with `hA`. Rewrite using `[Desc.embL, pullback.lift_fst]`.
-/
theorem isPullback_embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsPullback (Desc.toS N p hp) (Desc.embL N p hp) N.u (pullback.fst G.hom p) := by
  have hA : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π))
      (pullback.snd N.U.hom π) p := by
    have outer : IsPullback (Desc.toS N p hp ≫ pullback.fst N.U.hom π)
        (pullback.snd N.U.hom (pullback.fst π π ≫ π)) N.U.hom (p ≫ π) := by
      rw [Desc.toS, pullback.lift_fst, hp]
      exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right outer (by rw [Desc.toS, pullback.lift_snd]) (IsPullback.of_hasPullback _ _)
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback G.hom p)
  · rw [Desc.embL, pullback.lift_snd, N.u_over]
    exact hA
  · rw [Desc.embL, pullback.lift_fst]

/- English proof (translation)
Use `N.isOpen` as an intermediate fact. Conclude with `MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp) N.isOpen`.
-/
theorem isOpenImmersion_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsOpenImmersion (Desc.emb N p hp).left := by
  have := N.isOpen
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp) N.isOpen

/- English proof (translation)
Introduce `R _ _ _ _ S π _ _ _ G' _ _ hG N p p' hp hp' φ hsum hemb`. Establish `: Surjective N.U.hom` using `surjective_near N`. Establish `: GeometricallyIrreducible G'.hom` using `geometricallyIrreducible_of_semiAbelian G' hG`. Take `⟨_, hsm, hsep, _, _, _⟩` from `hG`. Establish `: IsOpenImmersion (Desc.emb N p hp).left` using `isOpenImmersion_emb N p hp`.

Establish `: Surjective (Desc.UT N).hom` using `by show Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance`. Establish `: Smooth ((Over.pullback p).obj G').hom` using `by show Smooth (pullback.snd G'.hom p); infer_instance`. Establish `: GeometricallyIrreducible ((Over.pullback p).obj G').hom` using `by show GeometricallyIrreducible (pullback.snd G'.hom p); infer_instance`. Establish `: IsSeparated ((Over.pullback p').obj G').hom` using `by show IsSeparated (pullback.snd G'.hom p'); infer_instance`. Use `isMonHom_of_open (Desc.emb N p hp) φ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Desc.sum N p hp ≫ φ = _`. Rewrite using `[hsum, Desc.sum, ← hemb]`.
-/
theorem isMonHom_of_sum_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  intro R _ _ _ _ S π _ _ _ G' _ _ hG N p p' hp hp' φ hsum hemb
  have : Surjective N.U.hom := surjective_near N
  have : GeometricallyIrreducible G'.hom := geometricallyIrreducible_of_semiAbelian G' hG
  obtain ⟨_, hsm, hsep, _, _, _⟩ := hG
  have : IsOpenImmersion (Desc.emb N p hp).left := isOpenImmersion_emb N p hp
  have : Surjective (Desc.UT N).hom := by
    show Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance
  have : Smooth ((Over.pullback p).obj G').hom := by
    show Smooth (pullback.snd G'.hom p); infer_instance
  have : GeometricallyIrreducible ((Over.pullback p).obj G').hom := by
    show GeometricallyIrreducible (pullback.snd G'.hom p); infer_instance
  have : IsSeparated ((Over.pullback p').obj G').hom := by
    show IsSeparated (pullback.snd G'.hom p'); infer_instance
  refine isMonHom_of_open (Desc.emb N p hp) φ ?_
  change Desc.sum N p hp ≫ φ = _
  rw [hsum, Desc.sum, ← hemb]

end GlobalTheory.Mum.DescHom
