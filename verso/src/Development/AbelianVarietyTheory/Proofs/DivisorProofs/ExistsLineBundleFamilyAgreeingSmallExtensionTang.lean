import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPicardClassExtendAffineMilnorSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismsIntoAffineOpenMilnorSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftAlongThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionDualNumberFibreProductAffineMilnorStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen.SmallExt

variable {S : Scheme.{0}}

/- English proof (translation)
Simplify using `[spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Simplify using `[spMap]`.
-/
theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

/- English proof (translation)
Use `⟨fun (x : PrimeSpectrum R) ↦ ?_⟩` and prove the remaining obligations. Establish `: x ∈ Set.range (PrimeSpectrum.comap φ)`. Rewrite using `[range_comap_of_surjective _ _ hφ]`. Introduce `a ha`. Take `⟨n, hn⟩` from `hn a ha`.

Conclude with `x.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)`. Conclude with `this`.
-/
theorem surjective_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Surjective φ)
    (hn : ∀ a ∈ RingHom.ker φ, IsNilpotent a) : Surjective (spMap φ) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ _ hφ]
    intro a ha
    obtain ⟨n, hn⟩ := hn a ha
    exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  exact this

/- English proof (translation)
Rewrite using `[MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]`.
-/
theorem pull_wl_comp {A X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (c : Pic (A ⊗ Z).left) :
    CechPic.pull (A ◁ (f ≫ g)).left c = CechPic.pull (A ◁ f).left (CechPic.pull (A ◁ g).left c) := by
  rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

/- English proof (translation)
Rewrite using `[MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]`.
-/
theorem pull_wl_id {A X : Over S} (c : Pic (A ⊗ X).left) : CechPic.pull (A ◁ 𝟙 X).left c = c := by
  rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]

end GlobalTheory.DualOpen.SmallExt

open GlobalTheory.DualOpen.SmallExt in

/- English proof (translation)
Introduce `S _ A _ hA U M hMf hMi hMt C _ _ e he hme hne s N hNf u' hsame`. Use `haveI : Smooth A.hom := hA.smooth`. Take `⟨P, _, i, p, σ, q, hpi, hσi, hqi, hσc, hσs, hM1, hM2⟩` from `GlobalTheory.T.smallExtension_dualNumber_fibreProduct_affineMilnorSquare C e he hme hne`. Establish `calc3` using `(GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.1`. Use `set k := IsLocalRing.ResidueField C`.

Use `set π : C →+* C ⧸ Ideal.span {e} := Ideal.Quotient.mk (Ideal.span {e})`. Use `set ρ : C →+* k := IsLocalRing.residue C`. Establish `hfi : (dnFst k).comp (dnInl k) = RingHom.id k` using `RingHom.ext fun x ↦ rfl`. Set `TC : Over S` to `Over.mk s`. Set `TP : Over S` to `Over.mk (spMap i ≫ s)`.

Set `Tε : Over S` to `Over.mk (spMap (dnInl k) ≫ spMap ρ ≫ s)`. Set `Tk : Over S` to `Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s)`. Set `jp : TC ⟶ TP` to `Over.homMk (spMap p) (by show spMap p ≫ spMap i ≫ s = s`. Rewrite using `[← Category.assoc, ← spMap_comp', hpi, spMap_id', Category.id_comp])`. Set `jσ : TC ⟶ TP` to `Over.homMk (spMap σ) (by show spMap σ ≫ spMap i ≫ s = s`.

Rewrite using `[← Category.assoc, ← spMap_comp', hσi, spMap_id', Category.id_comp])`. Set `jq : Tε ⟶ TP` to `Over.homMk (spMap q) (by show spMap q ≫ spMap i ≫ s = spMap (dnInl k) ≫ spMap ρ ≫ s`. Rewrite using `[← Category.assoc, ← spMap_comp', hqi, spMap_comp', Category.assoc])`. Set `r : TP ⟶ TC` to `Over.homMk (spMap i) rfl`. Set `kε : Tk ⟶ Tε` to `ptMap _ (dnFst k)`.

Set `kc : Tk ⟶ TC` to `Over.homMk (spMap ρ) (by show spMap ρ ≫ s = spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s`. Rewrite using `[← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])`. Set `k₀` to `ptMap s π`. Establish `hjr : jp ≫ r = 𝟙 _` using `Over.OverMorphism.ext (by show spMap p ≫ spMap i = 𝟙 _`. Rewrite using `[← spMap_comp', hpi, spMap_id'])`.

Establish `hσr : jσ ≫ r = 𝟙 _` using `Over.OverMorphism.ext (by show spMap σ ≫ spMap i = 𝟙 _`. Rewrite using `[← spMap_comp', hσi, spMap_id'])`. Establish `hsq : kε ≫ jq = kc ≫ jp` using `Over.OverMorphism.ext hM2.w.symm`. Establish `hkqr : kε ≫ jq ≫ r = kc` using `Over.OverMorphism.ext (by show spMap (dnFst k) ≫ spMap q ≫ spMap i = spMap ρ`. Rewrite using `[← spMap_comp' i q, hqi, spMap_comp', ← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])`.

Establish `hεs : Function.Surjective (dnFst k)` using `fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩`. Establish `hεn : ∀ a ∈ RingHom.ker (dnFst k), IsNilpotent a`. Introduce `a ha`. Establish `h0 : a.fst = 0` using `ha`. Use `⟨2, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext <;> simp [pow_two, h0]`. Establish `hπn : ∀ a ∈ RingHom.ker π, IsNilpotent a`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mk_ker]`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`.

Conclude with `⟨2, by rw [mul_pow, sq e, hme e he, mul_zero]⟩`. Establish `hkεs : Surjective kε.left` using `surjective_spMap _ hεs hεn`. Establish `hkεc : IsClosedImmersion kε.left` using `IsClosedImmersion.spec_of_surjective _ hεs`. Establish `hk₀s : Surjective k₀.left` using `surjective_spMap _ Ideal.Quotient.mk_surjective hπn`. Use `set n := cls N hNf.isLB`.

Use `set m := cls M hMf.isLB`. Establish `hd : CechPic.pull (A ◁ k₀).left (n - CechPic.pull (A ◁ u').left m) = 0`. Establish `h` using `(calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).1 hsame`. Rewrite using `[map_sub, h, pull_wl_comp, sub_self]`. Take `⟨d', hd'p, hd'σ⟩` from `GlobalTheory.T.exists_picardClass_extend_affineMilnorSquare S A TP TC TC _ jp jσ k₀ k₀ hM1 hσc hσs hk₀s _ hd`.

Establish `h3 : CechPic.pull (A ◁ kε).left (CechPic.pull (A ◁ jq).left d') = 0`. Rewrite using `[← pull_wl_comp, hsq, pull_wl_comp, hd'p, map_zero]`. Take `⟨D, hD, hDc⟩` from `cls_surj (CechPic.pull (A ◁ jq).left d')`. Establish `hDf : Fam A D` using `GlobalTheory.T.additiveFamily_of_trivial_mod_epsilon S A hA k (spMap (dnInl k) ≫ spMap ρ ≫ s) D hD (by rw [hDc]; exact h3)`. Take `⟨D₂, hD₂, hD₂c⟩` from `cls_surj (CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m)`.

Establish `hD₂f : Fam A D₂` using `(GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.1 Tε U Tε D M hDf hMf (𝟙 _) (jq ≫ r ≫ u') D₂ hD₂ (Or.inl (by rw [hD₂c, pull_wl_id, hDc]))`. Take `⟨v, hv⟩` from `hMt k (spMap ρ ≫ s) D₂ hD₂f (kε ≫ jq ≫ r ≫ u') ((calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).2 (by`. Rewrite using `[hD₂c, map_add, h3, zero_add, pull_wl_comp kε]))`. Establish `hv' : CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m = CechPic.pull (A ◁ v).left m`. Establish `h` using `(calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).1 hv`.

Rewrite `h` using `[pull_wl_id, hD₂c]`. Then use the resulting hypothesis. Establish `hglue : kc ≫ u' = kε ≫ v` using `hMi Tk _ _ ((calc3 _ _ _ M M hMf.isLB hMf.isLB _ _).2 (by`. Rewrite using `[← hkqr, Category.assoc, Category.assoc, pull_wl_comp kε (jq ≫ r ≫ u'), pull_wl_comp kε v, ← hv', map_add, h3, zero_add]))`. Take `⟨V, hVa, hV0, -⟩` from `exists_isAffineOpen_mem_and_subset (X := U.left) (U := ⊤) (x := u'.left (IsLocalRing.closedPoint C)) trivial`. Establish `hu'V : ∀ x, u'.left x ∈ V` using `fun x ↦ ((IsLocalRing.specializes_closedPoint (R := C) x).map u'.left.continuous).mem_open V.isOpen hV0`.

Establish `hvV : ∀ y, v.left y ∈ V`. Introduce `y`. Take `⟨z, rfl⟩` from `hkεs.surj y`. Establish `h` using `congrArg (fun f ↦ f.left z) hglue`. Simplify using `only [Over.comp_left, Scheme.Hom.comp_apply] at h`.

Rewrite using `[← h]`. Conclude with `hu'V _`. Take `⟨w, hw₁, hw₂⟩` from `GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare S U TP TC Tε Tk jp jq kc kε hM2 V hVa u' v hglue hu'V hvV`. Establish `hunit` using `GlobalTheory.T.abelianScheme_units_lift_along_thickening S A hA Tε Tk kε (inferInstanceAs (IsAffine (Sp (DualNumber k)))) hkεc hkεs`. Establish `hE` using `GlobalTheory.T.picardClass_eq_zero_affineMilnorSquare S A TP TC Tε Tk jp jq kc kε hM2 hunit (CechPic.pull (A ◁ w).left m - CechPic.pull (A ◁ (r ≫ u')).left m - d') (by`.

Rewrite using `[map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₁, ← Category.assoc, hjr, Category.id_comp, hd'p, sub_self, sub_zero]) (by`. Rewrite using `[map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₂, ← hv', add_sub_cancel_right, sub_self])`. Establish `hwe : CechPic.pull (A ◁ w).left m = CechPic.pull (A ◁ (r ≫ u')).left m + d'`. Rewrite `hE` using `[sub_sub]`. Conclude with `sub_eq_zero.1 hE`.

Use `⟨jσ ≫ w, (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[pull_wl_id, pull_wl_comp, hwe, map_add, ← pull_wl_comp, ← Category.assoc, hσr, Category.id_comp, hd'σ]`. Conclude with `(add_sub_cancel _ _).symm`.
-/
theorem GlobalTheory.DualOpen.exists_same_of_smallExt : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∀ u' : Over.mk s ⟶ U, Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) (ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u') → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  intro S _ A _ hA U M hMf hMi hMt C _ _ e he hme hne s N hNf u' hsame
  haveI : Smooth A.hom := hA.smooth
  obtain ⟨P, _, i, p, σ, q, hpi, hσi, hqi, hσc, hσs, hM1, hM2⟩ := GlobalTheory.T.smallExtension_dualNumber_fibreProduct_affineMilnorSquare C e he hme hne
  have calc3 := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.1
  set k := IsLocalRing.ResidueField C
  set π : C →+* C ⧸ Ideal.span {e} := Ideal.Quotient.mk (Ideal.span {e})
  set ρ : C →+* k := IsLocalRing.residue C
  have hfi : (dnFst k).comp (dnInl k) = RingHom.id k := RingHom.ext fun x ↦ rfl
  let TC : Over S := Over.mk s
  let TP : Over S := Over.mk (spMap i ≫ s)
  let Tε : Over S := Over.mk (spMap (dnInl k) ≫ spMap ρ ≫ s)
  let Tk : Over S := Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s)
  let jp : TC ⟶ TP := Over.homMk (spMap p) (by
    show spMap p ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hpi, spMap_id', Category.id_comp])
  let jσ : TC ⟶ TP := Over.homMk (spMap σ) (by
    show spMap σ ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hσi, spMap_id', Category.id_comp])
  let jq : Tε ⟶ TP := Over.homMk (spMap q) (by
    show spMap q ≫ spMap i ≫ s = spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hqi, spMap_comp', Category.assoc])
  let r : TP ⟶ TC := Over.homMk (spMap i) rfl
  let kε : Tk ⟶ Tε := ptMap _ (dnFst k)
  let kc : Tk ⟶ TC := Over.homMk (spMap ρ) (by
    show spMap ρ ≫ s = spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  let k₀ := ptMap s π
  have hjr : jp ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap p ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hpi, spMap_id'])
  have hσr : jσ ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap σ ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hσi, spMap_id'])
  have hsq : kε ≫ jq = kc ≫ jp := Over.OverMorphism.ext hM2.w.symm
  have hkqr : kε ≫ jq ≫ r = kc := Over.OverMorphism.ext (by
    show spMap (dnFst k) ≫ spMap q ≫ spMap i = spMap ρ
    rw [← spMap_comp' i q, hqi, spMap_comp', ← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  have hεs : Function.Surjective (dnFst k) := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  have hεn : ∀ a ∈ RingHom.ker (dnFst k), IsNilpotent a := by
    intro a ha
    have h0 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    ext <;> simp [pow_two, h0]
  have hπn : ∀ a ∈ RingHom.ker π, IsNilpotent a := by
    intro a ha
    rw [Ideal.mk_ker] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨2, by rw [mul_pow, sq e, hme e he, mul_zero]⟩
  have hkεs : Surjective kε.left := surjective_spMap _ hεs hεn
  have hkεc : IsClosedImmersion kε.left := IsClosedImmersion.spec_of_surjective _ hεs
  have hk₀s : Surjective k₀.left := surjective_spMap _ Ideal.Quotient.mk_surjective hπn

  set n := cls N hNf.isLB
  set m := cls M hMf.isLB
  have hd : CechPic.pull (A ◁ k₀).left (n - CechPic.pull (A ◁ u').left m) = 0 := by
    have h := (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).1 hsame
    rw [map_sub, h, pull_wl_comp, sub_self]
  obtain ⟨d', hd'p, hd'σ⟩ := GlobalTheory.T.exists_picardClass_extend_affineMilnorSquare S A TP TC TC _ jp jσ k₀ k₀ hM1 hσc hσs hk₀s _ hd
  have h3 : CechPic.pull (A ◁ kε).left (CechPic.pull (A ◁ jq).left d') = 0 := by
    rw [← pull_wl_comp, hsq, pull_wl_comp, hd'p, map_zero]
  obtain ⟨D, hD, hDc⟩ := cls_surj (CechPic.pull (A ◁ jq).left d')
  have hDf : Fam A D := GlobalTheory.T.additiveFamily_of_trivial_mod_epsilon S A hA k (spMap (dnInl k) ≫ spMap ρ ≫ s) D hD (by rw [hDc]; exact h3)
  obtain ⟨D₂, hD₂, hD₂c⟩ := cls_surj (CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m)
  have hD₂f : Fam A D₂ := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.1 Tε U Tε D M hDf hMf (𝟙 _) (jq ≫ r ≫ u') D₂ hD₂
    (Or.inl (by rw [hD₂c, pull_wl_id, hDc]))
  obtain ⟨v, hv⟩ := hMt k (spMap ρ ≫ s) D₂ hD₂f (kε ≫ jq ≫ r ≫ u') ((calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).2 (by
    rw [hD₂c, map_add, h3, zero_add, pull_wl_comp kε]))
  have hv' : CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m =
      CechPic.pull (A ◁ v).left m := by
    have h := (calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).1 hv
    rwa [pull_wl_id, hD₂c] at h
  have hglue : kc ≫ u' = kε ≫ v := hMi Tk _ _ ((calc3 _ _ _ M M hMf.isLB hMf.isLB _ _).2 (by
    rw [← hkqr, Category.assoc, Category.assoc, pull_wl_comp kε (jq ≫ r ≫ u'), pull_wl_comp kε v, ← hv', map_add,
      h3, zero_add]))
  obtain ⟨V, hVa, hV0, -⟩ := exists_isAffineOpen_mem_and_subset (X := U.left) (U := ⊤)
    (x := u'.left (IsLocalRing.closedPoint C)) trivial
  have hu'V : ∀ x, u'.left x ∈ V := fun x ↦
    ((IsLocalRing.specializes_closedPoint (R := C) x).map u'.left.continuous).mem_open V.isOpen hV0
  have hvV : ∀ y, v.left y ∈ V := by
    intro y
    obtain ⟨z, rfl⟩ := hkεs.surj y
    have h := congrArg (fun f ↦ f.left z) hglue
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [← h]
    exact hu'V _
  obtain ⟨w, hw₁, hw₂⟩ := GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare S U TP TC Tε Tk jp jq kc kε hM2 V hVa u' v hglue hu'V hvV
  have hunit := GlobalTheory.T.abelianScheme_units_lift_along_thickening S A hA Tε Tk kε (inferInstanceAs (IsAffine (Sp (DualNumber k)))) hkεc hkεs
  have hE := GlobalTheory.T.picardClass_eq_zero_affineMilnorSquare S A TP TC Tε Tk jp jq kc kε hM2 hunit
    (CechPic.pull (A ◁ w).left m - CechPic.pull (A ◁ (r ≫ u')).left m - d') (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₁, ← Category.assoc, hjr, Category.id_comp, hd'p,
        sub_self, sub_zero]) (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₂, ← hv', add_sub_cancel_right, sub_self])
  have hwe : CechPic.pull (A ◁ w).left m = CechPic.pull (A ◁ (r ≫ u')).left m + d' := by
    rw [sub_sub] at hE
    exact sub_eq_zero.1 hE
  refine ⟨jσ ≫ w, (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).2 ?_⟩
  rw [pull_wl_id, pull_wl_comp, hwe, map_add, ← pull_wl_comp, ← Category.assoc, hσr, Category.id_comp, hd'σ]
  exact (add_sub_cancel _ _).symm
