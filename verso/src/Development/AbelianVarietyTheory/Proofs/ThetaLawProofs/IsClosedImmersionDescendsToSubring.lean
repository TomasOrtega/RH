import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.ClosedLimit

universe u

/- English proof (translation)
Establish `h₁ : (⊤ : Subring B) ≤ f'.hom.range.comap b.hom`. Rewrite using `[← hs, Subring.closure_le]`. Introduce and unpack `_ (⟨y, rfl⟩ | hx)`. Conclude with `⟨a.hom y, congr($(po.w.symm).hom y)⟩`. Conclude with `h _ hx`.

Rewrite using `[← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]`. Introduce and unpack `_ (⟨y, rfl⟩ | hx)`. Conclude with `h₁ (Subring.mem_top y)`. Conclude with `hx`.
-/
theorem surjective_of_isPushout {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {a : A ⟶ A'} {b : B ⟶ B'}
    {f' : A' ⟶ B'} (po : IsPushout f a b f') (s : Set B)
    (hs : Subring.closure (Set.range f.hom ∪ s) = ⊤) (h : ∀ x ∈ s, b.hom x ∈ f'.hom.range) :
    Function.Surjective f'.hom := by
  have h₁ : (⊤ : Subring B) ≤ f'.hom.range.comap b.hom := by
    rw [← hs, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | hx)
    · exact ⟨a.hom y, congr($(po.w.symm).hom y)⟩
    · exact h _ hx
  rw [← RingHom.range_eq_top, ← top_le_iff,
    ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨y, rfl⟩ | hx)
  · exact h₁ (Subring.mem_top y)
  · exact hx

/- English proof (translation)
Establish `: IsAffine d.pt` using `Scheme.isAffine_of_isLimit _ hd`. Take `⟨_, hsurj⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine g`. Take `⟨i, hi⟩` from `Scheme.exists_isAffine_of_isLimit D c hc`. Establish `one (x : Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i), (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range`. Take `⟨y, hy⟩` from `hsurj ((c.π.app i).appTop x)`.

Take `⟨j, y, rfl⟩` from `exists_appTop_π_eq_of_isAffine_of_isLimit E d hd y`. Set `m` to `IsCofiltered.min i j`. Set `a : m ⟶ i` to `IsCofiltered.minToLeft i j`. Set `b : m ⟶ j` to `IsCofiltered.minToRight i j`. Establish `e₁ : c.π.app m ≫ D.map a = c.π.app i` using `c.w a`.

Establish `e₂ : c.π.app m ≫ α.app m ≫ E.map b = g ≫ d.π.app j`. Rewrite using `[← reassoc_of% hg, d.w b]`. Take `⟨l, f, hl⟩` from `exists_app_map_eq_map_of_isLimit D c hc (U := ⊤) isCompact_univ ((D.map a).appTop x) ((α.app m ≫ E.map b).appTop y) (by`. Establish `h₁ : (c.π.app m).appTop ((D.map a).appTop x) = (c.π.app i).appTop x` using `congr(($e₁).appTop x)`. Establish `h₂ : (c.π.app m).appTop ((α.app m ≫ E.map b).appTop y) = g.appTop ((d.π.app j).appTop y)` using `congr(($e₂).appTop y)`.

Conclude with `h₁.trans (hy.symm.trans h₂.symm))`. Use `⟨l, f ≫ a, (E.map f ≫ E.map b).appTop y, ?_⟩` and prove the remaining obligations. Establish `e₃ : α.app l ≫ E.map f ≫ E.map b = D.map f ≫ α.app m ≫ E.map b`. Rewrite using `[α.naturality_assoc]`. Establish `h₃ : (α.app l).appTop ((E.map f ≫ E.map b).appTop y) = (D.map f).appTop ((α.app m ≫ E.map b).appTop y)` using `congr(($e₃).appTop y)`.

Establish `h₄ : (D.map (f ≫ a)).appTop x = (D.map f).appTop ((D.map a).appTop x)` using `congr(($(D.map_comp f a)).appTop x)`. Conclude with `h₃.trans (hl.symm.trans h₄.symm)`. Establish `mono {j l : I} (f : j ⟶ i) (h : l ⟶ j) (x : Γ(D.obj i, ⊤)) (hx : (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range) : (D.map (h ≫ f)).appTop.hom x ∈ (α.app l).appTop.hom.range`. Take `⟨y, hy⟩` from `hx`. Use `⟨(E.map h).appTop y, ?_⟩` and prove the remaining obligations.

Establish `h₃ : (α.app l).appTop ((E.map h).appTop y) = (D.map h).appTop ((α.app j).appTop y)` using `congr(($((α.naturality h).symm)).appTop y)`. Establish `h₄ : (D.map (h ≫ f)).appTop x = (D.map h).appTop ((D.map f).appTop x)` using `congr(($(D.map_comp h f)).appTop x)`. Conclude with `h₃.trans ((congrArg _ hy).trans h₄.symm)`. Establish `many (s : Finset Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i), ∀ x ∈ s, (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => exact ⟨i, 𝟙 i, by simp⟩`. Consider the case `insert x s _ ih`. Take `⟨j₁, f₁, h₁⟩` from `ih`. Take `⟨j₂, f₂, h₂⟩` from `one x`. Take `⟨l, g₁, g₂, eg⟩` from `IsCofiltered.cospan f₁ f₂`.

Use `⟨l, g₁ ≫ f₁, fun y hy ↦ ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hy with rfl | hy` into its components or cases. Rewrite using `[eg]`. Conclude with `mono _ _ _ h₂`. Conclude with `mono _ _ _ (h₁ y hy)`.

Establish `hft : (α.app i).appTop.hom.FiniteType` using `HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance`. Set `_` to `(α.app i).appTop.hom.toAlgebra`. Take `⟨s, hs⟩` from `hft.out`. Take `⟨j, f, hj⟩` from `many s`. Establish `: IsAffine (D.obj j)` using `isAffine_of_isAffineHom (D.map f)`.

Use `⟨j, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩` and prove the remaining obligations. Use `surjective_of_isPushout (isPushout_appTop_of_isPullback (hα f)) s ?_ hj` and prove the remaining obligations. Conclude with `(Algebra.adjoin_eq_ring_closure (s : Set Γ(D.obj i, ⊤))).symm.trans (congrArg Subalgebra.toSubring hs)`.
-/
theorem exists_isClosedImmersion_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (α : D ⟶ E) (c : Cone D) (d : Cone E) (hc : IsLimit c) (hd : IsLimit d)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, IsAffine (E.obj i)]
    [∀ i, LocallyOfFiniteType (α.app i)]
    (hα : ∀ {i j} (f : i ⟶ j), IsPullback (D.map f) (α.app i) (α.app j) (E.map f))
    (g : c.pt ⟶ d.pt) [IsClosedImmersion g] (hg : ∀ i, g ≫ d.π.app i = c.π.app i ≫ α.app i) :
    ∃ i, IsClosedImmersion (α.app i) := by
  classical
  have : IsAffine d.pt := Scheme.isAffine_of_isLimit _ hd
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit D c hc
  have one (x : Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i),
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hsurj ((c.π.app i).appTop x)
    obtain ⟨j, y, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit E d hd y
    let m := IsCofiltered.min i j
    let a : m ⟶ i := IsCofiltered.minToLeft i j
    let b : m ⟶ j := IsCofiltered.minToRight i j
    have e₁ : c.π.app m ≫ D.map a = c.π.app i := c.w a
    have e₂ : c.π.app m ≫ α.app m ≫ E.map b = g ≫ d.π.app j := by
      rw [← reassoc_of% hg, d.w b]
    obtain ⟨l, f, hl⟩ := exists_app_map_eq_map_of_isLimit D c hc (U := ⊤) isCompact_univ
      ((D.map a).appTop x) ((α.app m ≫ E.map b).appTop y) (by
        have h₁ : (c.π.app m).appTop ((D.map a).appTop x) = (c.π.app i).appTop x :=
          congr(($e₁).appTop x)
        have h₂ : (c.π.app m).appTop ((α.app m ≫ E.map b).appTop y) =
          g.appTop ((d.π.app j).appTop y) := congr(($e₂).appTop y)
        exact h₁.trans (hy.symm.trans h₂.symm))
    refine ⟨l, f ≫ a, (E.map f ≫ E.map b).appTop y, ?_⟩
    have e₃ : α.app l ≫ E.map f ≫ E.map b = D.map f ≫ α.app m ≫ E.map b := by
      rw [α.naturality_assoc]
    have h₃ : (α.app l).appTop ((E.map f ≫ E.map b).appTop y) =
      (D.map f).appTop ((α.app m ≫ E.map b).appTop y) := congr(($e₃).appTop y)
    have h₄ : (D.map (f ≫ a)).appTop x = (D.map f).appTop ((D.map a).appTop x) :=
      congr(($(D.map_comp f a)).appTop x)
    exact h₃.trans (hl.symm.trans h₄.symm)
  have mono {j l : I} (f : j ⟶ i) (h : l ⟶ j) (x : Γ(D.obj i, ⊤))
      (hx : (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range) :
      (D.map (h ≫ f)).appTop.hom x ∈ (α.app l).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hx
    refine ⟨(E.map h).appTop y, ?_⟩
    have h₃ : (α.app l).appTop ((E.map h).appTop y) =
      (D.map h).appTop ((α.app j).appTop y) := congr(($((α.naturality h).symm)).appTop y)
    have h₄ : (D.map (h ≫ f)).appTop x = (D.map h).appTop ((D.map f).appTop x) :=
      congr(($(D.map_comp h f)).appTop x)
    exact h₃.trans ((congrArg _ hy).trans h₄.symm)
  have many (s : Finset Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i), ∀ x ∈ s,
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | insert x s _ ih =>
      obtain ⟨j₁, f₁, h₁⟩ := ih
      obtain ⟨j₂, f₂, h₂⟩ := one x
      obtain ⟨l, g₁, g₂, eg⟩ := IsCofiltered.cospan f₁ f₂
      refine ⟨l, g₁ ≫ f₁, fun y hy ↦ ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [eg]; exact mono _ _ _ h₂
      · exact mono _ _ _ (h₁ y hy)
  have hft : (α.app i).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  let _ := (α.app i).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  obtain ⟨j, f, hj⟩ := many s
  have : IsAffine (D.obj j) := isAffine_of_isAffineHom (D.map f)
  refine ⟨j, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  refine surjective_of_isPushout (isPushout_appTop_of_isPullback (hα f)) s ?_ hj
  exact (Algebra.adjoin_eq_ring_closure (s : Set Γ(D.obj i, ⊤))).symm.trans (congrArg Subalgebra.toSubring hs)

open GlobalTheory.Spread

section
variable {k : Type} [CommRing k] {X₀ Y₀ : Scheme.{0}} (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp k)

noncomputable def bcHom {T : Scheme.{0}} (t : T ⟶ Sp k) : pullback (g₀ ≫ q) t ⟶ pullback q t :=
  pullback.lift (pullback.fst _ _ ≫ g₀) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

@[reassoc]
/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _ @[reassoc]`.
-/
theorem bcHom_fst {T : Scheme.{0}} (t : T ⟶ Sp k) :
    bcHom g₀ q t ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g₀ := pullback.lift_fst _ _ _

@[reassoc]
/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem bcHom_snd {T : Scheme.{0}} (t : T ⟶ Sp k) :
    bcHom g₀ q t ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

/- English proof (translation)
Use `IsPullback.of_bot (v₂₁ := pullback.snd q t) (v₂₂ := q) (h₃₁ := t) ?_ (bcHom_fst g₀ q t).symm (.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[bcHom_snd]`. Conclude with `.of_hasPullback _ _`.
-/
theorem isPullback_bcHom {T : Scheme.{0}} (t : T ⟶ Sp k) :
    IsPullback (pullback.fst (g₀ ≫ q) t) (bcHom g₀ q t) g₀ (pullback.fst q t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q t) (v₂₂ := q) (h₃₁ := t) ?_
    (bcHom_fst g₀ q t).symm (.of_hasPullback _ _)
  rw [bcHom_snd]
  exact .of_hasPullback _ _

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := g₀) (h₂₂ := pullback.fst _ _) ?_ ?_ (isPullback_bcHom g₀ q _)` and prove the remaining obligations. Rewrite using `[bcMap_fst, bcMap_fst]`. Conclude with `isPullback_bcHom g₀ q _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, bcHom_fst, bcMap_fst_assoc, Category.assoc, bcMap_fst, bcHom_fst]`.

Rewrite using `[Category.assoc, bcHom_snd, bcMap_snd, Category.assoc, bcMap_snd, bcHom_snd_assoc]`.
-/
theorem isPullback_bcMap_bcHom {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) :
    IsPullback (bcMap (g₀ ≫ q) f) (bcHom g₀ q _) (bcHom g₀ q _) (bcMap q f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := g₀) (h₂₂ := pullback.fst _ _) ?_ ?_
    (isPullback_bcHom g₀ q _)
  · rw [bcMap_fst, bcMap_fst]
    exact isPullback_bcHom g₀ q _
  · apply pullback.hom_ext
    · rw [Category.assoc, bcHom_fst, bcMap_fst_assoc, Category.assoc, bcMap_fst, bcHom_fst]
    · rw [Category.assoc, bcHom_snd, bcMap_snd, Category.assoc, bcMap_snd, bcHom_snd_assoc]

/- English proof (translation)
Substitute `hm` using the available equality. Establish `: IsPullback (h.lift πX' (g' ≫ m) (by rw [Category.assoc, h'.w])) g' g m` using `IsPullback.of_right (by rw [h.lift_fst]; exact h') (h.lift_snd _ _ _) h`. Conclude with `MorphismProperty.of_isPullback this inferInstance`.
-/
theorem isClosedImmersion_of_isPullback {X Y X' Y' : Scheme.{0}} {g : X ⟶ Y} {πX : X ⟶ X₀}
    {πY : Y ⟶ Y₀} {g' : X' ⟶ Y'} {πX' : X' ⟶ X₀} {πY' : Y' ⟶ Y₀}
    (h : IsPullback πX g g₀ πY) (h' : IsPullback πX' g' g₀ πY') (m : Y' ⟶ Y) (hm : m ≫ πY = πY')
    [IsClosedImmersion g] : IsClosedImmersion g' := by
  subst hm
  have : IsPullback (h.lift πX' (g' ≫ m) (by rw [Category.assoc, h'.w])) g' g m :=
    IsPullback.of_right (by rw [h.lift_fst]; exact h') (h.lift_snd _ _ _) h
  exact MorphismProperty.of_isPullback this inferInstance

/- English proof (translation)
Set `α : bcDiagram (g₀ ≫ q) A ⟶ bcDiagram q A` to `{ app s := bcHom g₀ q _ naturality s t f := (isPullback_bcMap_bcHom g₀ q _).w }`. Establish `(s : (Finset A)ᵒᵖ) : IsAffine ((bcDiagram q A).obj s)` using `inferInstanceAs (IsAffine (pullback q (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))))`. Establish `(s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (α.app s)` using `MorphismProperty.of_isPullback (isPullback_bcHom g₀ q _) inferInstance`. Establish `: @IsClosedImmersion (bcCone (g₀ ≫ q) A).pt (bcCone q A).pt (bcHom g₀ q (spMap (algebraMap k A)))` using `‹_›`. Take `⟨s, hs⟩` from `exists_isClosedImmersion_of_isLimit _ _ α (bcCone (g₀ ≫ q) A) (bcCone q A) (isLimitBcCone _ _) (isLimitBcCone _ _) (fun f ↦ isPullback_bcMap_bcHom g₀ q _) (bcHom g₀ q (spMap (algebraMap k A))) (fun s ↦ (isPullback_bcMap_bcHom g₀ q _).w.symm)`.

Conclude with `⟨s.unop, hs⟩`.
-/
theorem exists_finset_bcHom (A : Type) [CommRing A] [Algebra k A] [IsAffine Y₀]
    [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀]
    [IsClosedImmersion (bcHom g₀ q (spMap (algebraMap k A)))] :
    ∃ s : Finset A, IsClosedImmersion
      (bcHom g₀ q (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))) := by
  classical
  let α : bcDiagram (g₀ ≫ q) A ⟶ bcDiagram q A :=
    { app s := bcHom g₀ q _
      naturality s t f := (isPullback_bcMap_bcHom g₀ q _).w }
  have (s : (Finset A)ᵒᵖ) : IsAffine ((bcDiagram q A).obj s) :=
    inferInstanceAs (IsAffine (pullback q
      (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))))
  have (s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (α.app s) :=
    MorphismProperty.of_isPullback (isPullback_bcHom g₀ q _) inferInstance
  have : @IsClosedImmersion (bcCone (g₀ ≫ q) A).pt (bcCone q A).pt
    (bcHom g₀ q (spMap (algebraMap k A))) := ‹_›
  obtain ⟨s, hs⟩ := exists_isClosedImmersion_of_isLimit _ _ α (bcCone (g₀ ≫ q) A) (bcCone q A)
    (isLimitBcCone _ _) (isLimitBcCone _ _) (fun f ↦ isPullback_bcMap_bcHom g₀ q _)
    (bcHom g₀ q (spMap (algebraMap k A))) (fun s ↦ (isPullback_bcMap_bcHom g₀ q _).w.symm)
  exact ⟨s.unop, hs⟩

end

/- English proof (translation)
Establish `hY' : IsPullback πY p q (spMap (algebraMap R₀ S))` using `hY`. Use `isClosedImmersion_of_isPullback g₀ hX (isPullback_bcHom g₀ q (spMap (algebraMap R₀ S))) hY'.isoPullback.inv hY'.isoPullback_inv_fst` as an intermediate fact. Take `⟨s, hs'⟩` from `exists_finset_bcHom g₀ q S`. Use `⟨s, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩` and prove the remaining obligations. Establish `hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁`.

Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hs hx`. Consider the case `algebraMap r => exact h r.2`. Consider the case `add x y _ _ hx hy => exact R₁.add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => exact R₁.mul_mem hx hy`. Set `i : Algebra.adjoin R₀ (s : Set S) →+* R₁` to `Subring.inclusion hle`. Establish `hi : spMap i ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) = spMap (Subring.inclusion h)`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.

Conclude with `isClosedImmersion_of_isPullback g₀ (isPullback_bcHom g₀ q (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))))) hX₁ (pullback.lift πY₁ (p₁ ≫ spMap i) (by rw [Category.assoc, hi, hY₁])) (pullback.lift_fst _ _ _)`.
-/
theorem descends_of_isAffine (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0})
    (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [IsAffine Y₀] [QuasiCompact g₀] [QuasiSeparated g₀]
    [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S)
    (hY : IsPullback πY p q (spMap R₀.subtype)) (hX : IsPullback πX g g₀ πY)
    (hg : IsClosedImmersion g) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁),
        πY₁ ≫ q = p₁ ≫ spMap (Subring.inclusion h) → IsPullback πX₁ g₁ g₀ πY₁ →
          IsClosedImmersion g₁ := by
  have hY' : IsPullback πY p q (spMap (algebraMap R₀ S)) := hY
  have := isClosedImmersion_of_isPullback g₀ hX (isPullback_bcHom g₀ q (spMap (algebraMap R₀ S)))
    hY'.isoPullback.inv hY'.isoPullback_inv_fst
  obtain ⟨s, hs'⟩ := exists_finset_bcHom g₀ q S
  refine ⟨s, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let i : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hi : spMap i ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact isClosedImmersion_of_isPullback g₀
    (isPullback_bcHom g₀ q (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))))) hX₁
    (pullback.lift πY₁ (p₁ ≫ spMap i) (by rw [Category.assoc, hi, hY₁])) (pullback.lift_fst _ _ _)

/- English proof (translation)
Establish `h` using `(IsPullback.of_hasPullback g (pullback.fst πY j)).paste_horiz hX`. Rewrite `h` using `[pullback.condition (f := πY)]`. Use `⟨pullback.lift (pullback.fst _ _ ≫ πX) (pullback.snd _ _ ≫ pullback.snd πY j) (by rw [h.w, Category.assoc]), ?_⟩` and prove the remaining obligations. Conclude with `IsPullback.of_right (by rw [pullback.lift_fst]; exact h) (pullback.lift_snd _ _ _) (.of_hasPullback _ _)`.
-/
theorem exists_isPullback_restrict {X₀ Y₀ X Y V : Scheme.{0}} {g₀ : X₀ ⟶ Y₀} {g : X ⟶ Y}
    {πX : X ⟶ X₀} {πY : Y ⟶ Y₀} (hX : IsPullback πX g g₀ πY) (j : V ⟶ Y₀) :
    ∃ m : pullback g (pullback.fst πY j) ⟶ pullback g₀ j,
      IsPullback m (pullback.snd _ _) (pullback.snd _ _) (pullback.snd πY j) := by
  have h := (IsPullback.of_hasPullback g (pullback.fst πY j)).paste_horiz hX
  rw [pullback.condition (f := πY)] at h
  refine ⟨pullback.lift (pullback.fst _ _ ≫ πX) (pullback.snd _ _ ≫ pullback.snd πY j)
    (by rw [h.w, Category.assoc]), ?_⟩
  exact IsPullback.of_right (by rw [pullback.lift_fst]; exact h) (pullback.lift_snd _ _ _)
    (.of_hasPullback _ _)

end GlobalTheory.ClosedLimit

namespace GlobalTheory

open ClosedLimit in

/- English proof (translation)
Introduce `S _ R₀ X₀ Y₀ X Y g₀ q _ _ _ _ g πX πY p hY hX hg`. Establish `: CompactSpace Y₀` using `QuasiCompact.compactSpace_of_compactSpace q`. Set `𝒰` to `Y₀.affineCover.finiteSubcover`. Establish `(i : 𝒰.I₀) : IsAffine (𝒰.X i)` using `inferInstance`. Establish `key (i : 𝒰.I₀)` using `descends_of_isAffine S R₀ _ _ _ _ (pullback.snd g₀ (𝒰.f i)) (𝒰.f i ≫ q) _ _ _ _ ((IsPullback.of_hasPullback πY (𝒰.f i)).flip.paste_vert hY) (exists_isPullback_restrict hX (𝒰.f i)).choose_spec inferInstance`.

Use `choose F hF using key`. Use `⟨Finset.univ.biUnion F, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩` and prove the remaining obligations. Use `(IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) (𝒰.pullback₁ πY₁)).mpr fun i ↦ ?_` and prove the remaining obligations. Conclude with `hF i R₁ h ((Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem F (Finset.mem_univ (α := 𝒰.I₀) i))).trans hs) _ _ _ _ _ _ ((IsPullback.of_hasPullback πY₁ (𝒰.f i)).flip.paste_vert hY₁).w (exists_isPullback_restrict hX₁ (𝒰.f i)).choose_spec`.
-/
theorem isClosedImmersion_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0}) (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [QuasiCompact q] [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S), IsPullback πY p q (spMap R₀.subtype) → IsPullback πX g g₀ πY → IsClosedImmersion g → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁), IsPullback πY₁ p₁ q (spMap (Subring.inclusion h)) → IsPullback πX₁ g₁ g₀ πY₁ → IsClosedImmersion g₁ := by
  classical
  intro S _ R₀ X₀ Y₀ X Y g₀ q _ _ _ _ g πX πY p hY hX hg
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace q
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstance
  have key (i : 𝒰.I₀) := descends_of_isAffine S R₀ _ _ _ _ (pullback.snd g₀ (𝒰.f i)) (𝒰.f i ≫ q) _ _ _ _
    ((IsPullback.of_hasPullback πY (𝒰.f i)).flip.paste_vert hY)
    (exists_isPullback_restrict hX (𝒰.f i)).choose_spec inferInstance
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (𝒰.pullback₁ πY₁)).mpr fun i ↦ ?_
  exact hF i R₁ h
    ((Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem F (Finset.mem_univ (α := 𝒰.I₀) i))).trans hs) _ _ _ _ _ _
    ((IsPullback.of_hasPullback πY₁ (𝒰.f i)).flip.paste_vert hY₁).w
    (exists_isPullback_restrict hX₁ (𝒰.f i)).choose_spec

end GlobalTheory
