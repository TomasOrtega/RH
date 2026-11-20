import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Take `⟨U, hU, hxU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show v (IsLocalRing.closedPoint T) ∈ (⊤ : X.Opens) from trivial)`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hr : Set.range v ⊆ Set.range hU'.fromSpec`. Rewrite using `[hU'.range_fromSpec]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `((IsLocalRing.specializes_closedPoint y).map v.continuous).mem_open U.isOpen hxU`. Establish `hv₁` using `IsOpenImmersion.lift_fac hU'.fromSpec v hr`. Rewrite `hv₁` using `[← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec v hr)]`. Use `set g := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec v hr) with hg`. Establish `hft₁ : (f.appLE ⊤ U le_top).hom.FiniteType` using `LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU' le_top`.

Establish `hft₀ : (algebraMap ℤ Γ(Spec (CommRingCat.of R), ⊤)).FiniteType`. Establish `h1 : (algebraMap ℤ R).FiniteType` using `RingHom.finiteType_algebraMap.2 inferInstance`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.surjective`. Use `h2.comp h1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Conclude with `RingHom.ext_int _ _`. Establish `hftU : (algebraMap ℤ Γ(X, U)).FiniteType`. Use `hft₁.comp hft₀` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`.

Establish `hftA : Algebra.FiniteType ℤ Γ(X, U)` using `RingHom.finiteType_algebraMap.1 hftU`. Take `⟨t, ht⟩` from `hftA.out`. Use `⟨t.image g.hom, fun S _ φ hφ hs => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ a : Γ(X, U), g.hom a ∈ φ.range`. Introduce `a`.

Establish `ha : a ∈ Algebra.adjoin ℤ (t : Set Γ(X, U))` using `by rw [ht]; exact Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem b hb`. Take `⟨c, hc⟩` from `hs (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))`. Conclude with `⟨c, hc⟩`.

Consider the case `algebraMap n => exact ⟨(n : S), by simp⟩`. Consider the case `add b c _ _ hb hc => rw [map_add]`. Conclude with `φ.range.add_mem hb hc`. Consider the case `mul b c _ _ hb hc => rw [map_mul]`. Conclude with `φ.range.mul_mem hb hc`.

Set `e : S ≃+* φ.range` to `RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩`. Set `g' : Γ(X, U) →+* S` to `(e.symm : φ.range →+* S).comp (g.hom.codRestrict φ.range hmem)`. Establish `hcomp : φ.comp g' = g.hom`. Use extensionality with `a`. Conclude with `congrArg Subtype.val (e.apply_symm_apply (g.hom.codRestrict φ.range hmem a))`.

Use `⟨Spec.map (CommRingCat.ofHom g') ≫ hU'.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[← hv₁, ← Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `a`. Conclude with `congrArg (fun h : Γ(X, U) →+* T => h a) hcomp`.
-/
theorem spec_local_point_descends {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] {T : Type} [CommRing T] [IsLocalRing T]
    (v : Spec (CommRingCat.of T) ⟶ X) :
    ∃ s : Finset T, ∀ (S : Type) [CommRing S] (φ : S →+* T), Function.Injective φ →
      (↑s : Set T) ⊆ Set.range φ → ∃ w : Spec (CommRingCat.of S) ⟶ X,
        Spec.map (CommRingCat.ofHom φ) ≫ w = v := by
  classical
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show v (IsLocalRing.closedPoint T) ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hr : Set.range v ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map v.continuous).mem_open U.isOpen hxU
  have hv₁ := IsOpenImmersion.lift_fac hU'.fromSpec v hr
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec v hr)] at hv₁
  set g := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec v hr) with hg

  have hft₁ : (f.appLE ⊤ U le_top).hom.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU' le_top
  have hft₀ : (algebraMap ℤ Γ(Spec (CommRingCat.of R), ⊤)).FiniteType := by
    have h1 : (algebraMap ℤ R).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.surjective
    have := h2.comp h1
    convert this using 1
    exact RingHom.ext_int _ _
  have hftU : (algebraMap ℤ Γ(X, U)).FiniteType := by
    have := hft₁.comp hft₀
    convert this using 1
    exact RingHom.ext_int _ _
  have hftA : Algebra.FiniteType ℤ Γ(X, U) := RingHom.finiteType_algebraMap.1 hftU
  obtain ⟨t, ht⟩ := hftA.out
  refine ⟨t.image g.hom, fun S _ φ hφ hs => ?_⟩
  have hmem : ∀ a : Γ(X, U), g.hom a ∈ φ.range := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (t : Set Γ(X, U)) := by rw [ht]; exact Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨c, hc⟩ := hs (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
      exact ⟨c, hc⟩
    | algebraMap n => exact ⟨(n : S), by simp⟩
    | add b c _ _ hb hc => rw [map_add]; exact φ.range.add_mem hb hc
    | mul b c _ _ hb hc => rw [map_mul]; exact φ.range.mul_mem hb hc
  let e : S ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  let g' : Γ(X, U) →+* S := (e.symm : φ.range →+* S).comp (g.hom.codRestrict φ.range hmem)
  have hcomp : φ.comp g' = g.hom := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (g.hom.codRestrict φ.range hmem a))
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ hU'.fromSpec, ?_⟩
  rw [← hv₁, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg (fun h : Γ(X, U) →+* T => h a) hcomp

end GlobalTheory
