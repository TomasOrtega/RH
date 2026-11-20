import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH
open GlobalTheory.Points

/- English proof (translation)
Establish `h1 : (s.appLE ⊤ W le_top).hom.FiniteType` using `HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top`. Establish `h2 : ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).FiniteType` using `RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective`. Establish `h3 : (algebraMap ℤ o).FiniteType` using `RingHom.finiteType_algebraMap.2 inferInstance`. Establish `h4` using `(h1.comp h2).comp h3`. Establish `h5 : (algebraMap ℤ Γ(X, W)).FiniteType`.

Use `h4 using 1` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`. Take `⟨t, ht⟩` from `(RingHom.finiteType_algebraMap.1 h5).out`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[Algebra.adjoin_int]`.

Conclude with `top_unique fun x _ => (show x ∈ subalgebraOfSubring (Subring.closure (t : Set Γ(X, W))) from ht ▸ Algebra.mem_top)`.
-/
theorem exists_finset_closure_eq_top {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {X : Scheme.{0}}
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ t : Finset Γ(X, W), Subring.closure (t : Set Γ(X, W)) = ⊤ := by
  have h1 : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h4 := (h1.comp h2).comp h3
  have h5 : (algebraMap ℤ Γ(X, W)).FiniteType := by
    convert h4 using 1
    exact RingHom.ext_int _ _
  obtain ⟨t, ht⟩ := (RingHom.finiteType_algebraMap.1 h5).out
  refine ⟨t, ?_⟩
  rw [Algebra.adjoin_int] at ht
  exact top_unique fun x _ => (show x ∈ subalgebraOfSubring (Subring.closure (t : Set Γ(X, W))) from
    ht ▸ Algebra.mem_top)

/- English proof (translation)
Establish `h1 : ∀ a, φ a ∈ j.range` using `fun a => (Subring.closure_le.2 (show t ⊆ (j.range.comap φ : Subring A) from h)) (ht ▸ Subring.mem_top a)`. Set `e : B ≃+* j.range` to `RingEquiv.ofBijective j.rangeRestrict ⟨fun _ _ hx => hj (congrArg Subtype.val hx), j.rangeRestrict_surjective⟩`. Use `⟨e.symm.toRingHom.comp (φ.codRestrict j.range h1), RingHom.ext fun a => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (e.apply_symm_apply ⟨φ a, h1 a⟩)`.
-/
theorem exists_factor_of_closure {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* C) (j : B →+* C)
    (hj : Function.Injective j) {t : Set A} (ht : Subring.closure t = ⊤) (h : ∀ a ∈ t, φ a ∈ j.range) :
    ∃ ψ : A →+* B, j.comp ψ = φ := by
  have h1 : ∀ a, φ a ∈ j.range := fun a =>
    (Subring.closure_le.2 (show t ⊆ (j.range.comap φ : Subring A) from h)) (ht ▸ Subring.mem_top a)
  let e : B ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hx => hj (congrArg Subtype.val hx), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict j.range h1), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, h1 a⟩)

/- English proof (translation)
Establish `hle : (⊤ : U₀.toScheme.Opens) ≤ U₀.ι ⁻¹ᵁ U₀` using `fun x _ => x.2`. Establish `hs : Function.Surjective (U₀.ι.appLE U₀ ⊤ hle).hom`. Establish `: IsIso (U₀.ι.appLE U₀ ⊤ hle)` using `inferInstance`. Conclude with `(asIso (U₀.ι.appLE U₀ ⊤ hle)).commRingCatIsoToRingEquiv.surjective`. Take `⟨f, hf⟩` from `hs ((u₀.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))`.

Establish `key : ∀ (L : Type) [Field L] (x : Sp L ⟶ U₀.toScheme), (Spec.preimage (x ≫ u₀)).hom a = valF (x ≫ U₀.ι) U₀ f`. Introduce `L _ x`. Rewrite using `[preimage_apply, ← valR_appLE x u₀ (U := ⊤) (V := ⊤) le_top (le_preimage_top _), ← hf, valR_appLE x U₀.ι hle (le_preimage_top _)]`. Both sides reduce to the same expression. Establish `hr : Set.range M.pt ⊆ Set.range U₀.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)`. Establish `h1` using `key Ω (IsOpenImmersion.lift U₀.ι M.pt hr)`. Rewrite `h1` using `[hu _ (IsOpenImmersion.lift_fac _ _ _), IsOpenImmersion.lift_fac, Spec.preimage_map]`. Rewrite using `[key K t]`.

Use `(RatModel.val_eq ?_ h1.symm).symm` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `(t w).2`.
-/
theorem preimage_comp_eq_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hne : (U₀ : Set M.Z).Nonempty) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R)
    (hu : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom)
    {K : Type} [Field K] (t : Sp K ⟶ U₀.toScheme) (a : R) :
    (Spec.preimage (t ≫ u₀)).hom a = M.val (t ≫ U₀.ι) a := by
  have hle : (⊤ : U₀.toScheme.Opens) ≤ U₀.ι ⁻¹ᵁ U₀ := fun x _ => x.2
  have hs : Function.Surjective (U₀.ι.appLE U₀ ⊤ hle).hom := by
    have : IsIso (U₀.ι.appLE U₀ ⊤ hle) := inferInstance
    exact (asIso (U₀.ι.appLE U₀ ⊤ hle)).commRingCatIsoToRingEquiv.surjective
  obtain ⟨f, hf⟩ := hs ((u₀.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  have key : ∀ (L : Type) [Field L] (x : Sp L ⟶ U₀.toScheme),
      (Spec.preimage (x ≫ u₀)).hom a = valF (x ≫ U₀.ι) U₀ f := by
    intro L _ x
    rw [preimage_apply, ← valR_appLE x u₀ (U := ⊤) (V := ⊤) le_top (le_preimage_top _), ← hf,
      valR_appLE x U₀.ι hle (le_preimage_top _)]
    rfl
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  have h1 := key Ω (IsOpenImmersion.lift U₀.ι M.pt hr)
  rw [hu _ (IsOpenImmersion.lift_fac _ _ _), IsOpenImmersion.lift_fac, Spec.preimage_map] at h1
  rw [key K t]
  refine (RatModel.val_eq ?_ h1.symm).symm
  rintro _ ⟨w, rfl⟩
  exact (t w).2

/- English proof (translation)
Introduce `o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y hy`. Establish `hO` using `hB.ov`. Set `w : Sp (PadicAlgCl p)` to `IsLocalRing.closedPoint (PadicAlgCl p)`. Establish `hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z)` using `hy ⟨w, rfl⟩`. Establish `hle : S.R ≤ M.O ((gPt p ≫ y) w)` using `hO.le.trans (RatModel.ringOn_le_O hw)`.

Set `y₀ : S.R →+* PadicAlgCl p` to `(RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom`. Establish `hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1` using `fun a => RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)`. Establish `hat : S.At M y y₀` using `fun _ => rfl`. Take `⟨W, hW, hyW, -⟩` from `exists_isAffineOpen_le y (le_preimage_top y)`. Use `haveI := hA.ft`.

Use `haveI := M.lft`. Take `⟨t, ht⟩` from `exists_finset_closure_eq_top M.s hW`. Use `⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hn, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hj : Function.Injective u.j` using `fun a b h => IsFractionRing.injective u.V (FractionRing u.V) ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))`. Take `⟨ψ, hψ⟩` from `exists_factor_of_closure (valMap y W hyW).hom u.j hj ht (by`.

Introduce `a ha`. Take `⟨x, hx⟩` from `hu _ (Finset.mem_image_of_mem _ ha)`. Take `⟨v, hv⟩` from `(u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))`. Conclude with `⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)`. Set `yV : Sp u.V ⟶ M.Z` to `Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec`.

Establish `hfac : spMap u.j ≫ yV = y`. Rewrite using `[← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]`. Both sides reduce to the same expression. Establish `hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y`. Establish `e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap u.j`.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[← hfac, ← Category.assoc, e, Category.assoc]`. Establish `hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]`. Rewrite `hw` using `[← hg]`. Conclude with `hw`. Use `⟨⟨hat, yV, hfac, IsOpenImmersion.lift U₀.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]`. Use `congr 1`. Use extensionality with `a`. Apply `(algebraMap (FractionRing u.V) (PadicAlgCl p)).injective` to reduce the goal to its premises. Establish `h1` using `preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_pt (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a`.

Rewrite `h1` using `[Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp, Spec.preimage_map]`. Conclude with `h1.trans (DFunLike.congr_fun u.fac a).symm`.
-/
theorem exists_fac_of_large_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → Nonempty (Q.Fac y u) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y hy
  have hO := hB.ov
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hn, fun u hu => ?_⟩
  have hj : Function.Injective u.j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom u.j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap u.j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap u.j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨⟨hat, yV, hfac, IsOpenImmersion.lift U₀.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_pt
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
