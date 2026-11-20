import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsCurvePullbackOfIsCurveBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsDedekindDomainAffineSectionsOfIsCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeAffineSectionsSubalgebraTensor
import Development.AutomorphicArithmetic.CommutativeAlgebra.SurjectiveOfIsPullbackSpecFieldExt

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Establish `: IsDomain R` using `Function.Injective.isDomain (e : R →+* S) e.injective`. Establish `: IsNoetherianRing R` using `isNoetherianRing_of_ringEquiv S e.symm`. Establish `: Ring.DimensionLEOne R` using `Ring.DimensionLEOne.of_ringEquiv e`. Establish `: IsIntegrallyClosed R` using `IsIntegrallyClosed.of_equiv e.symm`. Conclude with `{ }`.
-/
private theorem ded_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [IsDedekindDomain S] :
    IsDedekindDomain R := by
  have : IsDomain R := Function.Injective.isDomain (e : R →+* S) e.injective
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  exact { }

/- English proof (translation)
Rewrite using `[← Scheme.ΓSpecIso_naturality, hgen]`. Simplify using `only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField]`. Simplify using `only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`. Simplify using `only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]`. Simplify using `only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]`.

Use `erw [Iso.inv_hom_id, Category.comp_id]`. Both sides reduce to the same expression.
-/
private theorem base_comp {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom (algebraMap k C.functionField) =
      c.appLE ⊤ W le_top ≫ C.germToFunctionField W := by
  rw [← Scheme.ΓSpecIso_naturality, hgen]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Take `⟨y, rfl⟩` from `hu.surj w`. Conclude with `⟨y, hw⟩`.
-/
private theorem pre_ne {X Y : Scheme.{0}} (u : X ⟶ Y) (hu : Surjective u) (W : Y.Opens)
    (h : (W : Set Y).Nonempty) : ((u ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨y, rfl⟩ := hu.surj w
  exact ⟨y, hw⟩

/- English proof (translation)
Introduce `k _ _ C _ c hc _ hgen W _ hW B hB`. Establish `hWne : (W : Set C).Nonempty` using `⟨_, (Classical.arbitrary W).2⟩`. Take `⟨hC1, -⟩` from `UpperTheory.isDedekindDomain_affine_sections_of_isCurve k c hc`. Take `⟨hded, hnf⟩` from `hC1 W hW hWne`. Set `f : Γ(C, W) →+* C.functionField` to `(C.germToFunctionField W).hom`.

Establish `hmem : ∀ a, f a ∈ B`. Introduce `a`. Establish `: f a ∈ (B : Set C.functionField)`. Rewrite using `[hB]`. Conclude with `⟨a, rfl⟩`.

Conclude with `this`. Set `h : Γ(C, W) ≃+* B` to `RingEquiv.ofBijective (RingHom.codRestrict (σS := Subalgebra k C.functionField) f B hmem) ⟨fun a b hab => Scheme.germToFunctionField_injective C W (congrArg Subtype.val hab), fun b => by`. Establish `hb : (b : C.functionField) ∈ (B : Set C.functionField)` using `b.2`. Rewrite `hb` using `[hB]`. Take `⟨a, ha⟩` from `hb`.

Conclude with `⟨a, Subtype.ext ha⟩⟩`. Establish `hh : ∀ a, (h a : C.functionField) = f a` using `fun a => rfl`. Unfold `IsChart`. Use `⟨?_, ded_of_equiv h.symm, fun hf => hnf (MulEquiv.isField hf h.toMulEquiv), ?_, ?_⟩` and prove the remaining obligations. Use `haveI : LocallyOfFiniteType c := @IsProper.toLocallyOfFiniteType _ _ _ hc.2.1`.

Establish `g0` using `LocallyOfFiniteType.finiteType_of_affine_subset c (isAffineOpen_top (Sp k)) hW le_top`. Establish `gi : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, by simp⟩)`. Establish `g2` using `(g0.comp gi).comp_surjective (g := (h : Γ(C, W) →+* B)) h.surjective`. Rewrite using `[← RingHom.finiteType_algebraMap]`. Use `g2` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Use `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)) (base_comp c hgen W)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Rewrite `this` using `[← hh]`. Simplify using `using this`.

Establish `hfr` using `functionField_isFractionRing_of_isAffineOpen C W hW`. Use `(IsFractionRing.isFractionRing_iff_of_base_ringEquiv C.functionField h).mp hfr` as an intermediate fact. Establish `heq : ((algebraMap Γ(C, W) C.functionField).comp h.symm.toRingHom).toAlgebra = (inferInstance : Algebra B C.functionField)`. Apply `Algebra.algebra_ext` to reduce the goal to its premises. Introduce `b`.

Take `⟨a, rfl⟩` from `h.surjective b`. Use `show algebraMap Γ(C, W) _ (h.symm (h a)) = (h a : C.functionField)`. Rewrite using `[h.symm_apply_apply]`. Both sides reduce to the same expression. Rewrite `this` using `[heq]`.

Conclude with `this`. Introduce `L _ _ _`. Establish `hp` using `IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap k L)))`. Take `⟨hX, e, -, -⟩` from `UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c _ _ hp hgen W hW B hB`. Establish `hsurj` using `UpperTheory.surjective_of_isPullback_spec_field_ext k L c _ _ hp`.

Take `⟨hX1, -⟩` from `UpperTheory.isDedekindDomain_affine_sections_of_isCurve L _ (UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hc)`. Take `⟨hd2, hn2⟩` from `hX1 _ hX (pre_ne _ hsurj W hWne)`. Conclude with `⟨ded_of_equiv e, fun hf => hn2 (MulEquiv.isField hf e.symm.toMulEquiv)⟩`.
-/
theorem UpperTheory.isChart_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsChart B := by
  intro k _ _ C _ c hc _ hgen W _ hW B hB
  have hWne : (W : Set C).Nonempty := ⟨_, (Classical.arbitrary W).2⟩
  obtain ⟨hC1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve k c hc
  obtain ⟨hded, hnf⟩ := hC1 W hW hWne
  let f : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hmem : ∀ a, f a ∈ B := by
    intro a
    have : f a ∈ (B : Set C.functionField) := by
      rw [hB]; exact ⟨a, rfl⟩
    exact this
  let h : Γ(C, W) ≃+* B := RingEquiv.ofBijective
    (RingHom.codRestrict (σS := Subalgebra k C.functionField) f B hmem)
    ⟨fun a b hab => Scheme.germToFunctionField_injective C W (congrArg Subtype.val hab),
     fun b => by
      have hb : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
      rw [hB] at hb
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩
  have hh : ∀ a, (h a : C.functionField) = f a := fun a => rfl
  unfold IsChart
  refine ⟨?_, ded_of_equiv h.symm, fun hf => hnf (MulEquiv.isField hf h.toMulEquiv), ?_, ?_⟩
  · haveI : LocallyOfFiniteType c := @IsProper.toLocallyOfFiniteType _ _ _ hc.2.1
    have g0 := LocallyOfFiniteType.finiteType_of_affine_subset c (isAffineOpen_top (Sp k)) hW le_top
    have gi : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, by simp⟩)
    have g2 := (g0.comp gi).comp_surjective (g := (h : Γ(C, W) →+* B)) h.surjective
    rw [← RingHom.finiteType_algebraMap]
    convert g2
    ext x
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)) (base_comp c hgen W)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← hh] at this
    simpa using this
  · have hfr := functionField_isFractionRing_of_isAffineOpen C W hW
    have := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv C.functionField h).mp hfr
    have heq : ((algebraMap Γ(C, W) C.functionField).comp h.symm.toRingHom).toAlgebra =
        (inferInstance : Algebra B C.functionField) := by
      apply Algebra.algebra_ext
      intro b
      obtain ⟨a, rfl⟩ := h.surjective b
      show algebraMap Γ(C, W) _ (h.symm (h a)) = (h a : C.functionField)
      rw [h.symm_apply_apply]
      rfl
    rw [heq] at this
    exact this
  · intro L _ _ _
    have hp := IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    obtain ⟨hX, e, -, -⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c _ _ hp hgen W hW B hB
    have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c _ _ hp
    obtain ⟨hX1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve L _ (UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hc)
    obtain ⟨hd2, hn2⟩ := hX1 _ hX (pre_ne _ hsurj W hWne)
    exact ⟨ded_of_equiv e, fun hf => hn2 (MulEquiv.isField hf e.symm.toMulEquiv)⟩
